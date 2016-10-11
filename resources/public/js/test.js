var game = new Phaser.Game(800, 600, Phaser.AUTO, '', { preload: preload, create: create, update: update }, false, true, Phaser.Physics.ARCADE);

var contacts = [];
var chars = {};
var charsByTag = {};
var activeBodies = {
    body: []
};

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
    g.type = type;
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
    //todo: use char.type and char.tags
    var tchars = chars[char.type];
    quickRemove(tchars,char);
    for(var ti = 0; ti < char.tags.length; ti++) {
        var tagChars = charsByTag[char.tags[ti]];
        quickRemove(tagChars,char);
    }
}
function make_body(game,charType,charTags,char,bodyTags,shape,shapeParams) {
    //todo: don't assume rect or numeric constants!
    var s = game.make.sprite(shapeParams[0],shapeParams[1],char.type);
    s.tags = bodyTags;
    s.char = char;
    s.width = shapeParams[2];
    s.height = shapeParams[3];
    game.physics.arcade.enable(s);
    s.enable = false;
    return s;
}
function destroy_body(game,char,body) {
    deactivate_body(game,char,body);
    body.destroy();
}
function activate_body(game,char,body) {
    if(body.enable) {
        return;
    }
    char.add(body);
    var tags = body.tags;
    for(var ti = 0; ti < tags.length; ti++) {
        var t = tags[ti];
        var bodies = activeBodies[t];
        bodies.push(body);
    }
    body.enable = true;
    //todo: update body x,y,w,h based on variables?
}
function deactivate_body(game,char,body) {
    if(!body.enable) {
        return;
    }
    char.remove(body,false);
    body.enable = false;
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
    return false;
}

function contactBetween(c, achars, atags, bchars, btags) {
    return bodyMatches(c.a, achars, atags) && bodyMatches(c.b, bchars, btags);
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
}

var inputs;

function create() {
    game.physics.startSystem(Phaser.Physics.ARCADE);
    inputs = game.input.keyboard.addKeys({
        'flap': Phaser.KeyCode.SPACEBAR
    });
    make_char_flappy(game, "flappy", 64, 64, {}, {}, {});
}

function findContacts() {
    var ret = [];
    //write handlers to gather up contacts
    game.physics.arcade.collide(
        activeBodies.body, activeBodies.wall,
        function(b,w) {
            
        }
    );
    //collide body with walls
    //overlap everything else with everything else
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
