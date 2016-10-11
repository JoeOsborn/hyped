var game = new Phaser.Game(800, 600, Phaser.AUTO, '', { preload: preload, create: create, update: update }, false, true, Phaser.Physics.ARCADE);

var contacts = [];
var chars = {};
var charsByTag = {};
var activeBodies = {
    body: []
};
var walls;

function quickRemove(coll,obj) {
    if(!coll) { return; }
    for(var i = 0; i < coll.length; i++) {
        if(coll[i] == obj) {
            coll[i] = coll[coll.length-1];
            coll.length = coll.length - 1;
        }
    }
}

function make_container(game,name,tags,type,x,y) {
    var g = game.add.group(undefined,name);
    g.x = x;
    g.y = y;
    g.charType = type;
    g.tags = tags;
    //todo: tags, dispatch on right type
    for(var ti = 0; ti < tags.length; ti++) {
        var t = tags[ti];
        if(!(t in charsByTag)) { charsByTag[t] = []; }
        charsByTag[t].push(g);
    }
    if(!(type in chars)) { chars[type] = []; }
    chars[type].push(g);
    return g;
}
function destroy_container(game,char) {
    char.destroy(false);
    //todo: use char.charType and char.tags
    var tchars = chars[char.charType];
    quickRemove(tchars,char);
    for(var ti = 0; ti < char.tags.length; ti++) {
        var tagChars = charsByTag[char.tags[ti]];
        quickRemove(tagChars,char);
    }
}
function make_body(game,charType,charTags,char,bodyTags,shape,shapeParams) {
    //todo: don't assume rect or numeric constants!
    var s = game.make.sprite(shapeParams[0],shapeParams[1],char.charType);
    s.tags = bodyTags;
    s.char = char;
    s.width = shapeParams[2];
    s.height = shapeParams[3];
    game.physics.arcade.enable(s);
    s.body.setSize(s.width,s.height);
    s.body.enable = false;
    return s;
}
function destroy_body(game,char,body) {
    deactivate_body(game,char,body);
    body.destroy();
}
function activate_body(game,char,body) {
    if(body.body && body.body.enable) {
        return;
    }
    char.add(body);
    var tags = body.tags;
    for(var ti = 0; ti < tags.length; ti++) {
        var t = tags[ti];
        var bodies = activeBodies[t];
        bodies.push(body);
    }
    body.body.enable = true;
    char.updateTransform();
    body.updateTransform();
    //todo: update body position?
}
function deactivate_body(game,char,body) {
    if(!body.body || !body.body.enable) {
        return;
    }
    char.remove(body,false);
    body.body.enable = false;
    var tags = body.tags;
    for(var ti = 0; ti < tags.length; ti++) {
        var t = tags[ti];
        var bodies = activeBodies[t];
        quickRemove(bodies,body);
    }
}
function bodyMatches(body, chars, tags) {
    var i;
    if(chars) {
        var found = false;
        for(i = 0; i < chars.length; i++) {
            if(chars[i] == body.char) {
                found = true;
                break;
            }
        }
        if(!found) {
            return false;
        }
    }
    if(tags) {
        var allFound = true;
        for(var j = 0; j < body.tags.length; j++) {
            var thisFound = false;
            for(i = 0; i < tags.length; i++) {
                if(body.tags[j] == tags[i]) {
                    thisFound = true;
                    break;
                }
            }
            if(!thisFound) {
                allFound = false;
                break;
            }
        }
        if(!allFound) {
            return false;
        }
    }
    return true;
}

function contactBetween(c, achars, atags, bchars, btags) {
    return bodyMatches(c.a, achars, atags) && bodyMatches(c.b, bchars, btags);
}

function normalPresent(norm, norms) {
    for(var i = 0; i < norms.length; i++) {
        var dx = norms[i][0] - norm[0];
        var dy = norms[i][1] - norm[1];
        if(Math.abs(dx) < 0.01 && Math.abs(dy) < 0.01) {
            return true;
        }
    }
    return false;
}

function get_collisions(game,achars,atags,normals,bchars,btags) {
    //get bodies of achars with atags and bodies of bchars with btags
    var result = [];
    normals = normals || [[0,1],[1,0],[0,-1],[-1,0]];
    for(var i = 0; i < contacts.length; i++) {
        if(contactBetween(contacts[i], achars, atags, bchars, btags) &&
           normalPresent(contacts[i].normal, normals)) {
            result.push(contacts[i]);
        }
    }
    return result;
}
function get_chars(game,fromChars,type,tags) {
    var ret = [];
    var i;
    //todo
    if(type) {
        fromChars = charsWithType(fromChars,type);
    }
    if(tags) {
        fromChars = charsWithTags(fromChars,tags);
    }
    return fromChars;
}
function get_input(game,char,inputName) {
    return inputs[inputName].isDown;
}

setup_fn_flappy(
    make_container, destroy_container,
    make_body, destroy_body,
    activate_body, deactivate_body,
    get_collisions,
    get_chars,
    get_input
);

function preload() {
    game.load.image('flappy', 'images/flappy.png');
    game.load.image('wall', 'images/wall.png');
}

var inputs;

function create() {
    game.physics.startSystem(Phaser.Physics.ARCADE);
    inputs = game.input.keyboard.addKeys({
        'flap': Phaser.KeyCode.SPACEBAR
    });
    
    walls = game.add.group();
    //  We will enable physics for any object that is created in this group
    walls.enableBody = true;
    // Here we create the ground.
    var wall = walls.create(0, 300, 'wall');
    wall.tags = ["wall"];
    wall.body.immovable = true;
    wall.body.moves = false;
    wall.body.allowGravity = false;
    wall.width = game.world.width;
    wall.body.setSize(game.world.width,32);
    wall = walls.create(0, 0, 'wall');
    wall.tags = ["wall"];
    wall.body.immovable = true;
    wall.body.moves = false;
    wall.body.allowGravity = false;
    wall.body.setSize(game.world.width,32);
    
    make_char_flappy(game, "flappy", 128, 128, {}, {}, {});
}

var contacts = [];
function gatherContact(a,b) {
    //todo: handle overlaps properly. they're weird!
    var normal;
    if(a.x+a.width < b.x) {
        normal = [1,0];
    } else if(a.x > b.x + b.width) {
        normal = [-1,0];
    } else if(a.y > b.y + b.height) {
        normal = [0,-1];
    } else if(a.y + a.height < b.y) {
        normal = [0,1];
    }
    console.log("contact",a,b,normal);
    contacts.push({a:a,b:b,normal:normal});
}
function findContacts() {
    //todo: update body x,y,w,h based on variables?
    for(var bt in activeBodies) {
        var bodies = activeBodies[bt];
        for(var bi = 0; bi < bodies.length; bi++) {
            var b = bodies[bi];
            var c = b.char;
            b.updateTransform();
            //todo: need to update sprite position (b.x, b.y) based on shape
            // params if shape params are not constants.
            //todo: handle offsets as well
            b.body.x = c.x;
            b.body.y = c.y;
            b.body.velocity.x = c.vx;
            b.body.velocity.y = c.vy;
            b.body.acceleration.x = c.ax;
            b.body.acceleration.y = c.ay;
            //todo: update width and height based on shape params
            //b.body.setSize(b.width,b.height);
        }
    }

    contacts.length = 0;
    //collide 
    game.physics.arcade.collide(
        activeBodies.body, walls.children,
        gatherContact
    );
    //todo: collide other solid stuff

    //todo: then do overlap pairs, but these can't have regular normals right?

    //finally propagate velocities and positions back to the chars
    for(var bt in activeBodies) {
        //todo: handle other solid tags besides body
        if(bt != "body") { break; }
        var bodies = activeBodies[bt];
        for(var bi = 0; bi < bodies.length; bi++) {
            var b = bodies[bi];
            var bl = b.body.touching;
            if(bl &&
               (bl.left || bl.right || bl.up || bl.down)) {
                var c = b.char;
                //todo: need to update char position (c.x, c.y) based on shape
                // params if shape params are not constants.
                //todo: need to accommodate multiple solid bodies of a single character
                c.x = b.body.x;
                c.y = b.body.y;
                c.vx = b.body.velocity.x;
                c.vy = b.body.velocity.y;
                c.ax = b.body.acceleration.x;
                c.ay = b.body.acceleration.y;
            }
        }
    }

    return contacts;
}

function update() {
    var i;
    for(var ct in chars) {
        charSet = chars[ct];
        switch(ct) {
        case "flappy":
            for(i = 0; i < charSet.length; i++) {
                before_steps_flappy(game,charSet[i]);
            }
            for(i = 0; i < charSet.length; i++) {
                discrete_step_early_flappy(game,charSet[i]);
            }
            for(i = 0; i < charSet.length; i++) {
                discrete_step_late_flappy(game,charSet[i]);
            }
            for(i = 0; i < charSet.length; i++) {
                continuous_step_flappy(game,charSet[i],(1.0/30.0));
            }
            break;
        }
    }
    findContacts();
}
