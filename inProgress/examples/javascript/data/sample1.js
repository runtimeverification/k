"use strict";
var x = 1, y = 0; 
switch (x) {
	case 0 :
		x += 2;
		break;
	case "s" :
	case "t" :
		x -= 1;
		break;
	default:
		x = 0;
}

"{
    type: SCRIPT,
    0: {
        type: VAR,
        0: {
            type: IDENTIFIER,
            name: x,
        },
        1: {
            type: IDENTIFIER,
            end: 11,
            initializer: {
                type: NUMBER,
                value: 0
            },
            name: y,
        },
    },
    1: {
        type: SWITCH,
        cases: {
            type: CASE,
            caseLabel: {
                type: NUMBER,
                end: 39,
                lineno: 1,
                start: 38,
                tokenizer: [object Object],
                value: 0
            },
            end: 37,
            lineno: 1,
            start: 33,
            statements: {
                type: BLOCK,
                0: {
                    type: SEMICOLON,
                    end: 51,
                    expression: {
                        type: ASSIGN,
                        0: {
                            type: IDENTIFIER,
                            assignOp: null,
                            end: 47,
                            lineno: 1,
                            start: 46,
                            tokenizer: [object Object],
                            value: y
                        },
                        1: {
                            type: NUMBER,
                            end: 51,
                            lineno: 1,
                            start: 50,
                            tokenizer: [object Object],
                            value: 2
                        },
                        end: 51,
                        length: 2,
                        lineno: 1,
                        start: 46,
                        tokenizer: [object Object],
                        value: =
                    },
                    lineno: 1,
                    start: 46,
                    tokenizer: [object Object],
                    value: y
                },
                1: {
                    type: BREAK,
                    end: 61,
                    lineno: 1,
                    start: 56,
                    tokenizer: [object Object],
                    value: break
                },
                end: 61,
                length: 2,
                lineno: 1,
                start: 40,
                tokenizer: [object Object],
                value: :
            },
            tokenizer: [object Object],
            value: case
        },{
            type: CASE,
            caseLabel: {
                type: NUMBER,
                end: 71,
                lineno: 1,
                start: 70,
                tokenizer: [object Object],
                value: 1
            },
            end: 69,
            lineno: 1,
            start: 65,
            statements: {
                type: BLOCK,
                end: 73,
                lineno: 1,
                start: 72,
                tokenizer: [object Object],
                value: :
            },
            tokenizer: [object Object],
            value: case
        },{
            type: CASE,
            caseLabel: {
                type: NUMBER,
                end: 83,
                lineno: 1,
                start: 82,
                tokenizer: [object Object],
                value: 2
            },
            end: 81,
            lineno: 1,
            start: 77,
            statements: {
                type: BLOCK,
                0: {
                    type: SEMICOLON,
                    end: 96,
                    expression: {
                        type: ASSIGN,
                        0: {
                            type: IDENTIFIER,
                            assignOp: 24,
                            end: 91,
                            lineno: 1,
                            start: 90,
                            tokenizer: [object Object],
                            value: y
                        },
                        1: {
                            type: NUMBER,
                            end: 96,
                            lineno: 1,
                            start: 95,
                            tokenizer: [object Object],
                            value: 1
                        },
                        end: 96,
                        length: 2,
                        lineno: 1,
                        start: 90,
                        tokenizer: [object Object],
                        value: +
                    },
                    lineno: 1,
                    start: 90,
                    tokenizer: [object Object],
                    value: y
                },
                1: {
                    type: BREAK,
                    end: 106,
                    lineno: 1,
                    start: 101,
                    tokenizer: [object Object],
                    value: break
                },
                end: 106,
                length: 2,
                lineno: 1,
                start: 84,
                tokenizer: [object Object],
                value: :
            },
            tokenizer: [object Object],
            value: case
        },{
            type: DEFAULT,
            end: 117,
            lineno: 1,
            start: 110,
            statements: {
                type: BLOCK,
                0: {
                    type: SEMICOLON,
                    end: 131,
                    expression: {
                        type: ASSIGN,
                        0: {
                            type: IDENTIFIER,
                            assignOp: null,
                            end: 125,
                            lineno: 1,
                            start: 124,
                            tokenizer: [object Object],
                            value: y
                        },
                        1: {
                            type: NUMBER,
                            end: 131,
                            lineno: 1,
                            start: 128,
                            tokenizer: [object Object],
                            value: 100
                        },
                        end: 131,
                        length: 2,
                        lineno: 1,
                        start: 124,
                        tokenizer: [object Object],
                        value: =
                    },
                    lineno: 1,
                    start: 124,
                    tokenizer: [object Object],
                    value: y
                },
                end: 131,
                length: 1,
                lineno: 1,
                start: 118,
                tokenizer: [object Object],
                value: :
            },
            tokenizer: [object Object],
            value: default
        },
        defaultIndex: 3,
        discriminant: {
            type: IDENTIFIER,
            end: 27,
            lineno: 1,
            start: 26,
            tokenizer: [object Object],
            value: x
        },
        end: 24,
        lineno: 1,
        start: 18,
        tokenizer: [object Object],
        value: switch
    },
    2: {
        type: SEMICOLON,
        end: 146,
        expression: {
            type: ASSIGN,
            0: {
                type: IDENTIFIER,
                assignOp: 25,
                end: 140,
                lineno: 1,
                start: 139,
                tokenizer: [object Object],
                value: y
            },
            1: {
                type: NUMBER,
                end: 146,
                lineno: 1,
                start: 144,
                tokenizer: [object Object],
                value: 20
            },
            end: 146,
            length: 2,
            lineno: 1,
            start: 139,
            tokenizer: [object Object],
            value: -
        },
        lineno: 1,
        start: 139,
        tokenizer: [object Object],
        value: y
    },
    funDecls: ,
    length: 3,
    lineno: 1,
    tokenizer: [object Object],
    varDecls: {
        type: IDENTIFIER,
        end: 8,
        lineno: 1,
        name: x,
        readOnly: false,
        start: 7,
        tokenizer: [object Object],
        value: x
    },{
        type: IDENTIFIER,
        end: 11,
        initializer: {
            type: NUMBER,
            end: 15,
            lineno: 1,
            start: 14,
            tokenizer: [object Object],
            value: 0
        },
        lineno: 1,
        name: y,
        readOnly: false,
        start: 10,
        tokenizer: [object Object],
        value: y
    }
}"