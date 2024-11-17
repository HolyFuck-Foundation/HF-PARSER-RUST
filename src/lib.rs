#![no_std]

#[macro_use]
extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;

use core::iter::Peekable;

use thiserror_no_std::Error;

#[derive(Debug, Error, PartialEq)]
pub enum InternalTokenizerError {
    #[error("unexpected eof")]
    UnexpectedEof,
}

#[derive(Debug, Error, PartialEq)]
pub struct TokenizerError {
    pub error: InternalTokenizerError,
    pub location: (usize, usize),
}

#[derive(Debug, PartialEq)]
pub struct SourceToken {
    pub token: Token,
    pub location: (usize, usize),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Add,
    Subtract,
    MoveRight,
    MoveLeft,
    StackPush,
    StackPop,

    String(String),

    AsmStart,

    FuncDecl,
    FuncCall,

    ScopeStart,
    ScopeEnd,

    Jawns,
}

impl Token {
    fn token_offset(&self) -> (usize, usize) {
        match self {
            Self::String(s) => {
                let mut offset = (0, 0);

                for c in s.chars() {
                    if c == '\n' {
                        offset.0 += 1;
                        offset.1 = 0;
                    } else {
                        offset.1 += 1;
                    }
                }

                offset
            }
            _ => (0, 1),
        }
    }
}

enum Either<A, B> {
    A(A),
    B(B),
}

fn consume_string_until<I: Iterator<Item = char>>(
    i: &mut Peekable<I>,
    stop: char,
) -> Result<String, InternalTokenizerError> {
    let mut string = String::new();
    loop {
        if let Some(c) = i.peek() {
            match *c {
                c if c == stop => {
                    break;
                }
                c => {
                    string.push(c);
                    let _ = i.next(); // Consume the character
                }
            }
        } else {
            return Err(InternalTokenizerError::UnexpectedEof);
        }
    }
    Ok(string)
}

fn consume<I: Iterator<Item = char>>(
    mut i: Peekable<I>,
) -> Result<Vec<SourceToken>, TokenizerError> {
    let mut result = Vec::new();
    let mut location = (0, 0);

    while let Some(c) = i.next() {
        let either = match c {
            '+' => Either::A(vec![Token::Add]),
            '-' => Either::A(vec![Token::Subtract]),
            '>' => Either::A(vec![Token::MoveRight]),
            '<' => Either::A(vec![Token::MoveLeft]),
            '.' => Either::A(vec![Token::StackPush]),
            ',' => Either::A(vec![Token::StackPop]),

            ':' => Either::A(vec![
                Token::FuncDecl,
                Token::String(
                    consume_string_until(&mut i, '{')
                        .map_err(|e| TokenizerError { error: e, location })?,
                ),
            ]),
            '@' => Either::A(vec![
                Token::FuncCall,
                Token::String(
                    consume_string_until(&mut i, ';')
                        .map_err(|e| TokenizerError { error: e, location })?,
                ),
            ]),

            '{' => Either::A(vec![Token::ScopeStart]),
            '}' => Either::A(vec![Token::ScopeEnd]),

            ';' => Either::A(vec![Token::Jawns]),

            '$' => Either::A(vec![
                Token::AsmStart,
                Token::String(
                    consume_string_until(&mut i, ';')
                        .map_err(|e| TokenizerError { error: e, location })?,
                ),
            ]),

            c => Either::B(c),
        };
        match either {
            Either::A(tokens) => {
                for token in tokens {
                    let token_offset = token.token_offset();
                    result.push(SourceToken { token, location });
                    // This is for newlines in identifiers
                    if token_offset.0 > 0 {
                        location.0 += token_offset.0;
                        location.1 = 0;
                    }
                    location.1 += token_offset.1;
                }
            }
            Either::B(c) => match c {
                '\n' => {
                    location.0 += 1;
                    location.1 = 0;
                }
                _ => location.1 += 1,
            },
        }
    }

    Ok(result)
}

pub fn tokenize(code: &str) -> Result<Vec<SourceToken>, TokenizerError> {
    consume(code.chars().into_iter().peekable())
}

#[derive(Debug, PartialEq)]
pub enum SyntaxNode {
    Add,
    Subtract,
    MoveRight,
    MoveLeft,
    StackPush,
    StackPop,
    Function(String, Vec<AstNode>),
    FuncCall(String),
    Asm(String),
}

#[derive(Debug, PartialEq)]
pub struct AstNode {
    node: SyntaxNode,
    location: (usize, usize),
}

#[derive(Debug, PartialEq, Error)]
pub enum InternalSyntaxError {
    #[error("unexpected end of token stream")]
    UnexpectedEof,
    #[error("unexpected token: {0:?}")]
    UnexpectedToken(Token),
    #[error("unexpected token: {0:?}, instead expected {1:?}")]
    UnexpectedTokenExpected(Token, Token),
    #[error("expected token: {0:?}")]
    Expected(Token),
}

#[derive(Debug, PartialEq, Error)]
pub struct SyntaxError {
    location: (usize, usize),
    error: InternalSyntaxError,
}

pub fn build_syntax_tree(tokens: Vec<SourceToken>) -> Result<Vec<AstNode>, SyntaxError> {
    build_ast(&mut tokens.into_iter().peekable(), None)
}

fn build_ast<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    stop_at: Option<Token>,
) -> Result<Vec<AstNode>, SyntaxError> {
    let mut result = Vec::new();
    let mut stop_found = if stop_at.is_some() { false } else { true };

    while let Some(token) = tokens.next() {
        match token {
            SourceToken { token, .. } if Some(token.clone()) == stop_at => {
                stop_found = true;
                break;
            }
            SourceToken {
                token: Token::Add,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::Add,
                location,
            }),
            SourceToken {
                token: Token::Subtract,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::Subtract,
                location,
            }),
            SourceToken {
                token: Token::MoveRight,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::MoveRight,
                location,
            }),
            SourceToken {
                token: Token::MoveLeft,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::MoveLeft,
                location,
            }),
            SourceToken {
                token: Token::StackPush,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::StackPush,
                location,
            }),
            SourceToken {
                token: Token::StackPop,
                location,
            } => result.push(AstNode {
                node: SyntaxNode::StackPop,
                location,
            }),
            SourceToken {
                token: Token::FuncDecl,
                location,
            } => {
                let (name, body) = consume_function(tokens, location)?;
                result.push(AstNode {
                    node: SyntaxNode::Function(name, body),
                    location,
                });
            }
            SourceToken {
                token: Token::FuncCall,
                location,
            } => {
                let name = consume_match_string(tokens, location)?;
                let _ = consume_match_token(tokens, Token::Jawns, location)?;
                result.push(AstNode {
                    node: SyntaxNode::FuncCall(name),
                    location,
                });
            }
            SourceToken {
                token: Token::AsmStart,
                location,
            } => {
                let asm = consume_match_string(tokens, location)?;
                let _ = consume_match_token(tokens, Token::Jawns, location)?;
                result.push(AstNode {
                    node: SyntaxNode::Asm(asm),
                    location,
                });
            }
            SourceToken { token, location } => {
                return Err(SyntaxError {
                    location,
                    error: InternalSyntaxError::UnexpectedToken(token),
                });
            }
        }
    }

    if !stop_found {
        return Err(SyntaxError {
            location: (0, 0),
            error: InternalSyntaxError::Expected(stop_at.unwrap()),
        });
    }

    Ok(result)
}

fn consume_function<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<(String, Vec<AstNode>), SyntaxError> {
    let name = consume_match_string(tokens, location)?;
    let _ = consume_match_token(tokens, Token::ScopeStart, location)?;
    let mut body = Vec::new();
    while let Some(token) = tokens.peek() {
        match token {
            SourceToken {
                token: Token::ScopeEnd,
                ..
            } => {
                let _ = tokens.next();
                break;
            }
            // this will also fail if the scope end isnt found,
            // so the above check only needs to exist for the empty body case
            _ => body.append(&mut build_ast(tokens, Some(Token::ScopeEnd))?),
        }
    }
    Ok((name, body))
}

fn consume_match_string<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<String, SyntaxError> {
    if let Some(token) = tokens.next() {
        if let Token::String(string) = token.token {
            Ok(string)
        } else {
            Err(SyntaxError {
                location,
                error: InternalSyntaxError::UnexpectedTokenExpected(
                    token.token,
                    Token::String(String::new()),
                ),
            })
        }
    } else {
        Err(SyntaxError {
            location,
            error: InternalSyntaxError::Expected(Token::String(String::new())),
        })
    }
}

fn consume_match_token<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    token_to_match: Token,
    location: (usize, usize),
) -> Result<SourceToken, SyntaxError> {
    if let Some(token) = tokens.next() {
        if token.token == token_to_match {
            Ok(token)
        } else {
            Err(SyntaxError {
                location,
                error: InternalSyntaxError::UnexpectedTokenExpected(token.token, token_to_match),
            })
        }
    } else {
        Err(SyntaxError {
            location,
            error: InternalSyntaxError::Expected(token_to_match),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_hf() {
        const INPUT: &str = "++--<>.,";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::Add,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::Add,
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::Subtract,
                    location: (0, 2)
                },
                SourceToken {
                    token: Token::Subtract,
                    location: (0, 3)
                },
                SourceToken {
                    token: Token::MoveLeft,
                    location: (0, 4)
                },
                SourceToken {
                    token: Token::MoveRight,
                    location: (0, 5)
                },
                SourceToken {
                    token: Token::StackPush,
                    location: (0, 6)
                },
                SourceToken {
                    token: Token::StackPop,
                    location: (0, 7)
                },
            ]
        );
    }

    #[test]
    fn tokenize_func_decl() {
        const INPUT: &str = ":test{";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("test")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (0, 5)
                }
            ]
        )
    }

    #[test]
    fn tokenize_special() {
        const INPUT: &str = "+\n+ <  >";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::Add,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::Add,
                    location: (1, 0)
                },
                SourceToken {
                    token: Token::MoveLeft,
                    location: (1, 2)
                },
                SourceToken {
                    token: Token::MoveRight,
                    location: (1, 5)
                },
            ]
        )
    }

    #[test]
    fn tokenize_func_decl_newline() {
        const INPUT: &str = ":hi\n   t+st{";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("hi\n   t+st")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (1, 7)
                },
            ]
        )
    }

    #[test]
    fn tokenize_func_call() {
        const INPUT: &str = "@test;";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncCall,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("test")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::Jawns,
                    location: (0, 5),
                }
            ]
        )
    }

    #[test]
    fn tokenize_empty() {
        const INPUT: &str = "";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(result, vec![]);
    }

    #[test]
    fn tokenize_empty_function_name() {
        const INPUT: &str = ":{}";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeEnd,
                    location: (0, 2)
                }
            ]
        )
    }

    #[test]
    fn tokenize_space_function_name() {
        const INPUT: &str = ": \n\t {";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from(" \n\t ")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (1, 2)
                }
            ]
        )
    }

    #[test]
    fn tokenize_comment_only() {
        const INPUT: &str = "Hello World";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(result, vec![])
    }

    #[test]
    fn tokenize_asm() {
        const INPUT: &str = "$mov eax, 0;";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::AsmStart,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("mov eax, 0")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::Jawns,
                    location: (0, 11),
                }
            ]
        )
    }

    #[test]
    fn tokenize_asm_newline() {
        const INPUT: &str = "$mov eax,\n 0;";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::AsmStart,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("mov eax,\n 0")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::Jawns,
                    location: (1, 2),
                }
            ]
        )
    }

    #[test]
    fn tokenize_comments() {
        const INPUT: &str = "+this is a comment+ so is this";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::Add,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::Add,
                    location: (0, 18)
                },
            ]
        )
    }

    #[test]
    fn tokenize_function_inside_function() {
        const INPUT: &str = ":test{:test2{@test3;}}";
        let result = tokenize(INPUT).unwrap();
        assert_eq!(
            result,
            vec![
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 0)
                },
                SourceToken {
                    token: Token::String(String::from("test")),
                    location: (0, 1)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (0, 5)
                },
                SourceToken {
                    token: Token::FuncDecl,
                    location: (0, 6)
                },
                SourceToken {
                    token: Token::String(String::from("test2")),
                    location: (0, 7)
                },
                SourceToken {
                    token: Token::ScopeStart,
                    location: (0, 12)
                },
                SourceToken {
                    token: Token::FuncCall,
                    location: (0, 13)
                },
                SourceToken {
                    token: Token::String(String::from("test3")),
                    location: (0, 14)
                },
                SourceToken {
                    token: Token::Jawns,
                    location: (0, 19),
                },
                SourceToken {
                    token: Token::ScopeEnd,
                    location: (0, 20)
                },
                SourceToken {
                    token: Token::ScopeEnd,
                    location: (0, 21)
                }
            ]
        )
    }

    #[test]
    fn tokenizer_error_eof() {
        const INPUT: &str = ":test";
        let result = tokenize(INPUT);
        assert_eq!(
            result,
            Err(TokenizerError {
                error: InternalTokenizerError::UnexpectedEof,
                location: (0, 0) // the location of error is before the token which failed to parse
            })
        )
    }
    #[test]
    fn tokenizer_error_eof_func_call() {
        const INPUT: &str = "@test";
        let result = tokenize(INPUT);
        assert_eq!(
            result,
            Err(TokenizerError {
                error: InternalTokenizerError::UnexpectedEof,
                location: (0, 0) // the location of error is before the token which failed to parse
            })
        )
    }

    #[test]
    fn tokenizer_error_eof_asm() {
        const INPUT: &str = "$mov eax, 0";
        let result = tokenize(INPUT);
        assert_eq!(
            result,
            Err(TokenizerError {
                error: InternalTokenizerError::UnexpectedEof,
                location: (0, 0) // the location of error is before the token which failed to parse
            })
        )
    }

    #[test]
    fn ast_simple_function() {
        let input = vec![
            SourceToken {
                token: Token::FuncDecl,
                location: (0, 0),
            },
            SourceToken {
                token: Token::String(String::from("test")),
                location: (0, 1),
            },
            SourceToken {
                token: Token::ScopeStart,
                location: (0, 5),
            },
            SourceToken {
                token: Token::StackPop,
                location: (0, 6),
            },
            SourceToken {
                token: Token::StackPush,
                location: (0, 7),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 8),
            },
        ];
        let result = build_syntax_tree(input).unwrap();
        assert_eq!(
            result,
            vec![AstNode {
                node: SyntaxNode::Function(
                    String::from("test"),
                    vec![
                        AstNode {
                            node: SyntaxNode::StackPop,
                            location: (0, 6),
                        },
                        AstNode {
                            node: SyntaxNode::StackPush,
                            location: (0, 7),
                        },
                    ]
                ),
                location: (0, 0),
            }]
        );
    }
}
