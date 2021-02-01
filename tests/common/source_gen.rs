//! Provides unit tests easy ways to generate compilable source files from statements, when they
//! don't really care that much about the metadata.

#![allow(unused)]

use truth::Game;

pub struct Format {
    pub cmd: &'static str,
    pub game: Game,
    pub script_head: &'static str,
    /// Embed a series of statements inside some sort of subroutine definition;
    /// whatever is appropriate for the language in question.
    pub make_main: fn(&str) -> String,
}

pub const ANM_06: Format = Format {
    cmd: "truanm",
    game: Game::Th06,
    script_head: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    width: 512,
    height: 512,
    offset_x: 0,
    offset_y: 0,
    format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {
        sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0},
        sprite1: {id: 1, x: 0.0, y: 0.0, w: 512.0, h: 480.0},
        sprite2: {id: 2, x: 0.0, y: 0.0, w: 512.0, h: 480.0},
        sprite3: {id: 3, x: 0.0, y: 0.0, w: 512.0, h: 480.0},
        sprite4: {id: 4, x: 0.0, y: 0.0, w: 512.0, h: 480.0},
    },
}
"#,
    make_main: |body| format!(r#"
script script0 {{
    {}
}}
"#, body),
};

pub const ANM_10: Format = Format {
    cmd: "truanm",
    game: Game::Th10,
    script_head: ANM_06.script_head,
    make_main: ANM_06.make_main,
};

pub const STD_08: Format = Format {
    cmd: "trustd",
    game: Game::Th08,
    script_head: r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "dm",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {},
    instances: [],
}
"#,
    make_main: |body| format!(r#"
script main {{
    {}
}}
"#, body),
};

pub const MSG_06: Format = Format {
    cmd: "trumsg",
    game: Game::Th06,
    script_head: r#"
#pragma mapfile "map/any.msgm"
"#,
    make_main: |body| format!(r#"
script main {{
    {}
}}
"#, body),
};
