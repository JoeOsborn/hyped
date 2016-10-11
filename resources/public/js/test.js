var game = new Phaser.Game(800, 600, Phaser.AUTO, '', { preload: preload, create: create, update: update });

var flappys = [];
var bodies = [];
var walls = [];

function make_container(game,name,tags,type,x,y) {
    var g = game.add.group(undefined,name);
    g.x = x;
    g.y = y;
    g.type = type;
    g.tags = tags;
    //todo: tags, dispatch on right type
    flappys.push(g);
    return g;
}
function destroy_container(game,char) {
    char.destroy(false);
    //todo: use char.type and char.tags
    for(var i = 0; i < flappys.length; i++) {
        if(flappys[i] == char) {
            flappys[i] = flappys[flappys.length-1];
            flappys.length = flappys.length - 1;
        }
    }
}
function make_body(game,charType,charTags,char,bodyTags,shape,shapeParams) {
    //todo: don't assume rect or numeric constants!
    var s = game.make.sprite(shapeParams[0],shapeParams[1],char.type);
    s.tags = bodyTags;
    s.width = shapeParams[2];
    s.height = shapeParams[3];
    return s;
}
function destroy_body(game,char,body) {
    body.destroy();
    for(var i = 0; i < bodies.length; i++) {
        if(bodies[i] == body) {
            bodies[i] = bodies[bodies.length - 1];
            bodies.length = bodies.length - 1;
        }
    }
}
function activate_body(game,char,body) {
    char.add(body);
    //todo: update body x,y,w,h based on variables?
}
function deactivate_body(game,char,body) {
    char.remove(body,false);
}
function get_collisions(game,achars,atags,normals,bchars,btags) {
    //todo
    return [];
}
function get_chars(game,fromChars,tags) {
    return flappys;
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
    inputs = game.input.keyboard.addKeys({
        'flap': Phaser.KeyCode.SPACEBAR
    });
    make_char_flappy(game, "flappy", 64, 64, {}, {}, {});
}

function update() {
    var i;
    for(i = 0; i < flappys.length; i++) {
        before_steps_flappy(game,flappys[i]);
    }
    for(i = 0; i < flappys.length; i++) {
        discrete_step_early_flappy(game,flappys[i]);
    }
    for(i = 0; i < flappys.length; i++) {
        discrete_step_late_flappy(game,flappys[i]);
    }
    for(i = 0; i < flappys.length; i++) {
        continuous_step_flappy(game,flappys[i],(1.0/30.0));
    }
}
