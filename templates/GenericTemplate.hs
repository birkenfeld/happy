// -----------------------------------------------------------------------------
// Some convenient typedefs

const ERROR_TOK: isize = 1;

enum Cont {
    Loop(isize, isize),
    NewToken,
    Accept(isize),
}

// Types to be defined by the user: Token, Error, State

type Res<T> = Result<T, Error>;
type Action = fn(&mut Parser, isize, isize) -> Res<Cont>;
type Stack = Vec<HappyAbsSyn>;

pub struct Parser {
    pub user: State,
    token: Token,
    stack: Stack,
    state: Action,
    states: Vec<Action>,
}

impl Parser {
    pub fn exec<F, T>(initial_state: State, do_parse: F) -> Res<(State, T)>
        where F: FnOnce(&mut Parser) -> Res<T>
    {
        let mut parser = Parser {
            user: initial_state,
            token: CToken::CTokEof,
            state: happyInvalid,
            states: vec![],
            stack: vec![]
        };
        let res = do_parse(&mut parser)?;
        Ok((parser.user, res))
    }
}


fn happyInvalid(_: &mut Parser, _: isize, _: isize) -> Res<Cont> {
    panic!("parser not initialized correctly")
}

// -----------------------------------------------------------------------------
// Starting the parse

fn happyParse(p: &mut Parser, start_state: Action) -> Res<HappyAbsSyn> {
    p.state = start_state;
    p.states.clear();
    p.stack.clear();
    p.stack.push(HappyAbsSyn::HappyErrorToken(0));
    let mut cont = Cont::NewToken;

    loop {
        cont = match cont {
            Cont::Loop(i, j) => (p.state)(p, i, j)?,
            Cont::NewToken => happyNewToken(p)?,
            Cont::Accept(j) => return happyAccept(p, j),
        }
    }
}

// -----------------------------------------------------------------------------
// Accepting the parse
//
// If the current token is ERROR_TOK, it means we've just accepted a partial
// parse (a %partial parser).  We must ignore the saved token on the top of
// the stack in this case.

fn happyAccept(p: &mut Parser, j: isize) -> Res<HappyAbsSyn> {
    match j {
        ERROR_TOK if p.stack.len() > 1 => {
            p.stack.pop();
            Ok(p.stack.pop().unwrap())
        }
        _ => Ok(p.stack.pop().unwrap())
    }
}

// -----------------------------------------------------------------------------
// Shifting a token

fn happyShift(p: &mut Parser, new_state: Action, i: isize) -> Res<Cont> {
    match i {
        ERROR_TOK => {
            let x = p.stack.pop().unwrap();
            let i = match x {
                HappyErrorToken(i) => i,
                _ => unreachable!(),
            };

            p.states.push(new_state);
            p.state = new_state;
            Ok(Cont::Loop(i, i))
        }
        _ => {
            p.states.push(p.state);
            p.stack.push(HappyTerminal(p.token.clone()));
            p.state = new_state;
            Ok(Cont::NewToken)
        },
    }
}

// -----------------------------------------------------------------------------
// happyReduce is specialised for the common cases.

fn happySpecReduce_0(p: &mut Parser, nt: isize, val: HappyAbsSyn, j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            p.states.push(p.state);
            p.stack.push(val);
            Ok(Cont::Loop(nt, j))
        },
    }
}

fn happySpecReduce_1(p: &mut Parser, nt: isize,
                     reducer: fn(HappyAbsSyn) -> HappyAbsSyn, j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            let v1 = p.stack.pop().unwrap();
            p.state = *p.states.last().unwrap();
            let val = reducer(v1);
            p.stack.push(val);
            Ok(Cont::Loop(nt, j))
        }
    }
}

fn happySpecReduce_2(p: &mut Parser, nt: isize,
                     reducer: fn(HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn, j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            let v1 = p.stack.pop().unwrap();
            let v2 = p.stack.pop().unwrap();
            p.states.pop();
            p.state = *p.states.last().unwrap();
            let val = reducer(v1, v2);
            p.stack.push(val);
            Ok(Cont::Loop(nt, j))
        }
    }
}

fn happySpecReduce_3(p: &mut Parser, nt: isize,
                     reducer: fn(HappyAbsSyn, HappyAbsSyn, HappyAbsSyn) -> HappyAbsSyn,
                     j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            let v1 = p.stack.pop().unwrap();
            let v2 = p.stack.pop().unwrap();
            let v3 = p.stack.pop().unwrap();
            p.states.pop();
            p.states.pop();
            p.state = *p.states.last().unwrap();
            let val = reducer(v1, v2, v3);
            p.stack.push(val);
            Ok(Cont::Loop(nt, j))
        }
    }
}

fn happyReduce(p: &mut Parser, k: isize, nt: isize, reducer: fn(&mut Parser), j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            for _ in 0..k - 1 {
                p.states.pop();
            }
            p.state = *p.states.last().unwrap();
            reducer(p);
            Ok(Cont::Loop(nt, j))
        }
    }
}

fn happyResultReduce(p: &mut Parser, k: isize, nt: isize,
                     reducer: fn(&mut Parser) -> Res<HappyAbsSyn>, j: isize) -> Res<Cont> {
    match j {
        ERROR_TOK => happyFail(p, ERROR_TOK),
        j => {
            p.states.push(p.state);
            for _ in 0..k {
                p.states.pop();
            }
            p.state = *p.states.last().unwrap();
            let val = reducer(p)?;
            p.stack.push(val);
            Ok(Cont::Loop(nt, j))
        }
    }
}

// -----------------------------------------------------------------------------
// Moving to a new state after a reduction

fn happyGoto(p: &mut Parser, action: Action, j: isize) -> Res<Cont> {
    p.state = action;
    action(p, j, j)
}

// -----------------------------------------------------------------------------
// Error recovery (ERROR_TOK is the error token)

fn happyFail(p: &mut Parser, i: isize) -> Res<Cont> {
    match i {
        ERROR_TOK if p.stack.len() > 0 => happyError_(p, i),
        i => {
            p.stack.push(HappyErrorToken(i));
            (p.state)(p, ERROR_TOK, ERROR_TOK)
        },
    }
}

fn notHappyAtAll<a: 'static>() -> a {
    panic!("Internal Happy error")
}

// end of Happy Template.
