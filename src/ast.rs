use core::{fmt::Formatter, iter::Peekable};

use alloc::{string::String, vec::Vec};
use thiserror_no_std::Error;

use crate::token::{SourceToken, Token};

#[derive(Debug, PartialEq, Clone)]
pub enum SyntaxNode {
    Add,
    Subtract,
    MoveRight,
    MoveLeft,
    StackPush,
    StackPop,
    MemAlloc(usize),
    Function(String, Vec<AstNode>),
    FuncCall(String),
    ExternalFunctionCall(String),
    Condition(Vec<AstNode>),
}

#[derive(PartialEq, Clone)]
pub struct AstNode {
    pub node: SyntaxNode,
    pub location: (usize, usize),
}

impl core::fmt::Debug for AstNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        if f.alternate() && matches!(self.node, SyntaxNode::Function(_, _))
            || matches!(self.node, SyntaxNode::Condition(_))
        {
            write!(
                f,
                "{:#?} \x1b[90m({}:{})\x1b[0m",
                self.node,
                self.location.0 + 1,
                self.location.1 + 1
            )
        } else {
            write!(
                f,
                "{:?} \x1b[90m({}:{})\x1b[0m",
                self.node,
                self.location.0 + 1,
                self.location.1 + 1
            )
        }
    }
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
    #[error("invalid number: {0:?}")]
    InvalidNumber(Token),
}

#[derive(Debug, PartialEq, Error)]
pub struct SyntaxError {
    pub location: (usize, usize),
    pub error: InternalSyntaxError,
}

impl SyntaxError {
    pub fn span(&self) -> (usize, usize) {
        match &self.error {
            InternalSyntaxError::UnexpectedToken(token) => token.token_offset(),
            InternalSyntaxError::UnexpectedTokenExpected(token, _) => token.token_offset(),
            InternalSyntaxError::Expected(token) => token.token_offset(),
            InternalSyntaxError::InvalidNumber(token) => token.token_offset(),
            _ => (0, 1),
        }
    }
}

pub fn build_ast(tokens: Vec<SourceToken>) -> Result<Vec<AstNode>, SyntaxError> {
    build_ast_impl(&mut tokens.into_iter().peekable(), None)
}

fn build_ast_impl<I: Iterator<Item = SourceToken>>(
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
                token: Token::MemAlloc,
                location,
            } => {
                let byte_count = consume_mem_alloc(tokens, location)?;
                result.push(AstNode {
                    node: SyntaxNode::MemAlloc(byte_count),
                    location,
                });
            }
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
                    node: SyntaxNode::ExternalFunctionCall(asm),
                    location,
                });
            }
            SourceToken {
                token: Token::CondStart,
                location,
            } => {
                let body = consume_condition(tokens, location)?;
                result.push(AstNode {
                    node: SyntaxNode::Condition(body),
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

fn consume_mem_alloc<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<usize, SyntaxError> {
    let byte_count = consume_match_number(tokens, location)?;
    let _ = consume_match_token(tokens, Token::Jawns, location)?;
    Ok(byte_count)
}

fn consume_function<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<(String, Vec<AstNode>), SyntaxError> {
    let name = consume_match_string(tokens, location)?;
    let _ = consume_match_token(tokens, Token::ScopeStart, location)?;
    let mut body = Vec::new();
    if let Some(token) = tokens.peek() {
        match token {
            SourceToken {
                token: Token::ScopeEnd,
                ..
            } => {
                let _ = tokens.next();
            }
            // this will also fail if the scope end isnt found,
            // so the above check only needs to exist for the empty body case
            _ => body.append(&mut build_ast_impl(tokens, Some(Token::ScopeEnd))?),
        }
    } else {
        return Err(SyntaxError {
            location,
            error: InternalSyntaxError::UnexpectedEof,
        });
    }
    Ok((name, body))
}

fn consume_condition<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<Vec<AstNode>, SyntaxError> {
    let mut body = Vec::new();
    if let Some(token) = tokens.peek() {
        match token {
            SourceToken {
                token: Token::CondEnd,
                ..
            } => {
                let _ = tokens.next();
            }
            // this will also fail if the cond end isnt found,
            // so the above check only needs to exist for the empty cond body case
            _ => body.append(&mut build_ast_impl(tokens, Some(Token::CondEnd))?),
        }
    } else {
        return Err(SyntaxError {
            location,
            error: InternalSyntaxError::UnexpectedEof,
        });
    }
    Ok(body)
}

fn consume_match_number<I: Iterator<Item = SourceToken>>(
    tokens: &mut Peekable<I>,
    location: (usize, usize),
) -> Result<usize, SyntaxError> {
    if let Some(token) = tokens.next() {
        if let Token::String(number_str) = &token.token {
            let number = number_str.parse().map_err(|_| SyntaxError {
                location,
                error: InternalSyntaxError::InvalidNumber(token.token),
            })?;
            Ok(number)
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
        let result = build_ast(input).unwrap();
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

    #[test]
    fn ast_function_with_missing_scope_end() {
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
        ];
        let result = build_ast(input);
        assert_eq!(
            result,
            Err(SyntaxError {
                error: InternalSyntaxError::Expected(Token::ScopeEnd),
                location: (0, 0),
            })
        );
    }

    #[test]
    fn ast_function_with_missing_scope_start() {
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
                token: Token::StackPop,
                location: (0, 6),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 8),
            },
        ];
        let result = build_ast(input);
        assert_eq!(
            result,
            Err(SyntaxError {
                error: InternalSyntaxError::UnexpectedTokenExpected(
                    Token::StackPop,
                    Token::ScopeStart
                ),
                location: (0, 0),
            })
        );
    }

    #[test]
    fn ast_function_with_missing_func_name() {
        let input = vec![
            SourceToken {
                token: Token::FuncDecl,
                location: (0, 0),
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
                token: Token::ScopeEnd,
                location: (0, 8),
            },
        ];
        let result = build_ast(input);
        assert_eq!(
            result,
            Err(SyntaxError {
                error: InternalSyntaxError::UnexpectedTokenExpected(
                    Token::ScopeStart,
                    Token::String(String::new())
                ),
                location: (0, 0),
            })
        );
    }

    #[test]
    fn ast_function_with_missing_func_decl() {
        let input = vec![
            SourceToken {
                token: Token::ScopeStart,
                location: (0, 5),
            },
            SourceToken {
                token: Token::String(String::from("test")),
                location: (0, 1),
            },
            SourceToken {
                token: Token::StackPop,
                location: (0, 6),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 8),
            },
        ];
        let result = build_ast(input);
        assert_eq!(
            result,
            Err(SyntaxError {
                error: InternalSyntaxError::UnexpectedToken(Token::ScopeStart),
                location: (0, 5),
            })
        );
    }

    #[test]
    fn ast_no_function() {
        let input = vec![
            SourceToken {
                token: Token::StackPop,
                location: (0, 0),
            },
            SourceToken {
                token: Token::StackPush,
                location: (0, 1),
            },
        ];
        let result = build_ast(input).unwrap();
        assert_eq!(
            result,
            vec![
                AstNode {
                    node: SyntaxNode::StackPop,
                    location: (0, 0),
                },
                AstNode {
                    node: SyntaxNode::StackPush,
                    location: (0, 1),
                },
            ]
        );
    }

    #[test]
    fn ast_function_within_function() {
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
                token: Token::FuncDecl,
                location: (0, 10),
            },
            SourceToken {
                token: Token::String(String::from("test2")),
                location: (0, 11),
            },
            SourceToken {
                token: Token::ScopeStart,
                location: (0, 16),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 19),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 20),
            },
        ];
        let result = build_ast(input).unwrap();
        assert_eq!(
            result,
            vec![AstNode {
                node: SyntaxNode::Function(
                    String::from("test"),
                    vec![AstNode {
                        node: SyntaxNode::Function(String::from("test2"), vec![]),
                        location: (0, 10),
                    }],
                ),
                location: (0, 0),
            }]
        );
    }

    #[test]
    fn ast_test_all_primitive_types() {
        let input = vec![
            SourceToken {
                token: Token::Add,
                location: (0, 0),
            },
            SourceToken {
                token: Token::Subtract,
                location: (0, 1),
            },
            SourceToken {
                token: Token::MoveRight,
                location: (0, 2),
            },
            SourceToken {
                token: Token::MoveLeft,
                location: (0, 3),
            },
            SourceToken {
                token: Token::StackPush,
                location: (0, 4),
            },
            SourceToken {
                token: Token::StackPop,
                location: (0, 5),
            },
            SourceToken {
                token: Token::FuncDecl,
                location: (0, 6),
            },
            SourceToken {
                token: Token::String(String::from("func_name")),
                location: (0, 7),
            },
            SourceToken {
                token: Token::ScopeStart,
                location: (0, 8),
            },
            SourceToken {
                token: Token::ScopeEnd,
                location: (0, 9),
            },
            SourceToken {
                token: Token::FuncCall,
                location: (0, 10),
            },
            SourceToken {
                token: Token::String(String::from("func_call")),
                location: (0, 11),
            },
            SourceToken {
                token: Token::Jawns,
                location: (0, 12),
            },
            SourceToken {
                token: Token::AsmStart,
                location: (0, 13),
            },
            SourceToken {
                token: Token::String(String::from("external_fn")),
                location: (0, 14),
            },
            SourceToken {
                token: Token::Jawns,
                location: (0, 15),
            },
        ];
        let result = build_ast(input).unwrap();
        assert_eq!(
            result,
            vec![
                AstNode {
                    node: SyntaxNode::Add,
                    location: (0, 0),
                },
                AstNode {
                    node: SyntaxNode::Subtract,
                    location: (0, 1),
                },
                AstNode {
                    node: SyntaxNode::MoveRight,
                    location: (0, 2),
                },
                AstNode {
                    node: SyntaxNode::MoveLeft,
                    location: (0, 3),
                },
                AstNode {
                    node: SyntaxNode::StackPush,
                    location: (0, 4),
                },
                AstNode {
                    node: SyntaxNode::StackPop,
                    location: (0, 5),
                },
                AstNode {
                    node: SyntaxNode::Function(String::from("func_name"), vec![]),
                    location: (0, 6),
                },
                AstNode {
                    node: SyntaxNode::FuncCall(String::from("func_call")),
                    location: (0, 10),
                },
                AstNode {
                    node: SyntaxNode::ExternalFunctionCall(String::from("external_fn")),
                    location: (0, 13),
                },
            ]
        );
    }

    #[test]
    fn ast_condition_block() {
        let input = vec![
            SourceToken {
                token: Token::CondStart,
                location: (0, 0),
            },
            SourceToken {
                token: Token::Add,
                location: (0, 1),
            },
            SourceToken {
                token: Token::CondEnd,
                location: (0, 2),
            },
        ];
        let result = build_ast(input).unwrap();
        assert_eq!(
            result,
            vec![AstNode {
                node: SyntaxNode::Condition(vec![AstNode {
                    node: SyntaxNode::Add,
                    location: (0, 1),
                }]),
                location: (0, 0),
            }]
        );
    }

    #[test]
    fn ast_mem_alloc() {
        let input = vec![
            SourceToken {
                token: Token::MemAlloc,
                location: (0, 0),
            },
            SourceToken {
                token: Token::String(String::from("10")),
                location: (0, 1),
            },
            SourceToken {
                token: Token::Jawns,
                location: (0, 3),
            },
        ];
        let result = build_ast(input).unwrap();
        assert_eq!(
            result,
            vec![AstNode {
                node: SyntaxNode::MemAlloc(10),
                location: (0, 0),
            }]
        )
    }

    #[test]
    fn ast_mem_alloc_invalid() {
        let input = vec![
            SourceToken {
                token: Token::MemAlloc,
                location: (0, 0),
            },
            SourceToken {
                token: Token::String(String::from("fake")),
                location: (0, 1),
            },
            SourceToken {
                token: Token::Jawns,
                location: (0, 5),
            },
        ];
        let result = build_ast(input);
        assert_eq!(
            result,
            Err(SyntaxError {
                error: InternalSyntaxError::InvalidNumber(Token::String(String::from("fake"))),
                location: (0, 0),
            })
        )
    }
}
