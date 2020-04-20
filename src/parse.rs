#![allow(dead_code)]
//use crate::cons::{Cons};

use std::fmt;
use std::vec::Vec;
use std::str::Chars;
use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;
use crate::type_sy::{Type};
use crate::type_sy::{t_fun, t_con, t_var_0, t_param};
use crate::template::{Template, TemplateBit};

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
pub enum ParseError{
    ParseError{
        msg: String,
        source: Box<ParseError>
    },
    ParseErrorBottom{
        msg: String,
        line: usize,
        following: String,
    },
}

fn parse_error(msg: &str, source: ParseError) -> ParseError{
    ParseError::ParseError{
        msg: String::from(msg),
        source: Box::new(source),
    }
}

fn parse_error_bottom<T>(msg: &str, stream: &mut State<T>) -> ParseError
where T: Iterator<Item = char>
{
    ParseError::ParseErrorBottom{
        msg: String::from(msg),
        line: stream.current_line,
        following: stream.take(20).collect(),
    }
}


impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ParseError::ParseError{msg, source} =>
                write!(f, "{} Caused by: {}", msg, source),
            ParseError::ParseErrorBottom{msg, line, following} =>
                write!(f, "{} Line {} Following: {}", msg, line, following),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
        // self.source_err.map(|e| &*e)
    }
}

pub fn parse_constructors<T>(stream: &mut State<T>) -> Result<Vec<(String, Type, Vec<String>, Template)>, ParseError>
    where T: Iterator<Item = char>,
{
    let res = parse_many(
        |s| {
            let cons_list = parse_cons(s)
                .map_err(|e| parse_error("parse_constructors: failed parsing cons.", e))?;
            Ok(cons_list)
        },
        stream)?;

    parse_end_of_stream(stream)
    .map_err(|e| parse_error("parse_constructors: expected end of stream", e))?;

    Ok(res)
}

pub fn parse_cons<T>(stream: &mut State<T>) -> Result<(String, Type, Vec<String>, Template), ParseError>
    where T: Iterator<Item = char>
{
    let (name1, typ) = parse_cons_declaration(stream)
    .map_err(|e| parse_error("parse_cons: failed parsing declaration.", e))?;

    parse_char('\n',stream)
    .map_err(|e| parse_error("parse_cons_definition: expecting newline", e))?;
    
    let (name2, args, body) = parse_cons_definition(stream)
    .map_err(|e| parse_error("parse_cons: failed parsing definition.", e))?;

    if name1 != name2 {
        Err(parse_error_bottom("parse_cons: function name in declaration does not match function name in definition", stream))
    } else {
        Ok((name1, typ, args, body))
    }
}

pub fn parse_cons_declaration<T>(stream: &mut State<T>) -> Result<(String, Type), ParseError>
    where T: Iterator<Item = char>
{
    let name = parse_cons_name(stream)
        .map_err(|e| parse_error("parse_cons_declaration: failed parsing name", e))?;
    parse_char(':', stream)
        .map_err(|e| parse_error("parse_cons_declaration: failed parsing colon delimiter", e))?;
    skip_whitespace(stream)?;
    let t = parse_type(stream)
        .map_err(|e| parse_error("parse_cons_declaration: failed parsing type", e))?;
    Ok((name, t))
}

pub fn parse_cons_definition<T>(stream: &mut State<T>) -> Result<(String, Vec<String>, Template), ParseError>
where T: Iterator<Item = char>
{
    let (name, args) = parse_cons_args(stream)
    .map_err(|e| parse_error("parse_cons_definition: failed parsing cons args", e))?;

    parse_char('\n',stream)
    .map_err(|e| parse_error("parse_cons_definition: expecting newline", e))?;

    let body = parse_cons_body(stream)
    .map_err(|e| parse_error("parse_cons_definition: failed parsing cons body", e))?;

    Ok((name, args, body))
}

pub fn parse_cons_args<T>(stream: &mut State<T>) -> Result<(String, Vec<String>), ParseError>
where T: Iterator<Item = char>
{
    let name = parse_cons_name(stream)
        .map_err(|e| parse_error("parse_cons_args: failed parsing cons name", e))?;
    let args = parse_many(parse_cons_arg_name, stream)
        .map_err(|e| parse_error("parse_cons_args: failed parsing args names", e))?;

    Ok((name, args))
}

pub fn parse_cons_arg_name<T>(stream: &mut State<T>) -> Result<String, ParseError>
where T: Iterator<Item = char>
{
    parse_uncapitalized_identifier(stream)
    .map_err(|e| parse_error("parse_cons_arg_name: failed.", e))
}

pub fn parse_cons_body<T>(stream: &mut State<T>) -> Result<Template, ParseError>
where T: Iterator<Item = char>
{
    pub fn parse_arg<T>(stream: &mut State<T>) -> Result<String, ParseError>
    where T: Iterator<Item = char>
    {
        parse_parenthesized('{', '}', parse_uncapitalized_identifier, stream)
    }

    pub fn parse_body_line<T>(stream: &mut State<T>) -> Result<Vec<TemplateBit>, ParseError>
    where T: Iterator<Item = char>
    {
        parse_string("> ", stream)
        .map_err(|e| parse_error("parse_body_line: failed parsing line prefix", e))?;

        let indent : usize = parse_many(parse_whitespace, stream)?.len();

        let mut template_bits: Vec<TemplateBit> = Vec::new();

        match try_parse(parse_arg, stream) {
            Ok(arg) => template_bits.push(TemplateBit::Key(indent, arg)),
            Err(_) => (),
        }

        loop {
            match try_parse(parse_empty_line, stream) {
                Ok(_) => {
                    match template_bits.last_mut() {
                        None => template_bits.push(TemplateBit::Raw('\n'.to_string())),
                        Some(last) => match last {
                            TemplateBit::Raw(s) => s.push('\n'),
                            TemplateBit::Key(_, _) =>
                                template_bits.push(TemplateBit::Raw('\n'.to_string())),
                        }
                    }
                    break
                }
                Err(_) => (),
            };
            match try_parse(parse_arg, stream) {
                Ok(arg) => {
                    template_bits.push(TemplateBit::Key(0, arg));
                    continue
                },
                Err(_) => (),
            };
            match try_parse(parse_any_char, stream) {
                Ok(c) => {
                    match template_bits.last_mut() {
                        None => template_bits.push(TemplateBit::Raw(c.to_string())),
                        Some(last) => match last {
                            TemplateBit::Raw(s) => s.push(c),
                            TemplateBit::Key(_, _) =>
                                template_bits.push(TemplateBit::Raw(c.to_string())),
                        }
                    }
                },
                Err(_) => break, //reaches end of stream
            };
        }

        Ok(template_bits)
    }

    let lines = parse_many(parse_body_line, stream)
    .map_err(|e| parse_error("parse_cons_body: failed parsing a line of body", e))?;

    skip_empty_lines(stream)?;

    Ok(Template(lines.into_iter().flatten().collect()))
}

pub fn parse_cons_name<T>(stream: &mut State<T>) -> Result<String, ParseError>
where T: Iterator<Item = char>
{
    parse_uncapitalized_identifier(stream)
    .map_err(|e| parse_error("parse_cons_name: failed.", e))
}

pub fn parse_type<T>(stream: &mut State<T>) -> Result<Type, ParseError>
    where T: Iterator<Item = char>
{
    parse_alt(
        parse_function_type,
        |s| parse_alt(
            parse_parametric_type,
            |s| parse_alt(
                parse_type_constant,
                parse_type_variable,
                s),
            s),
        stream)
    .map_err(|e| parse_error("parse_type: failed", e))
}

pub fn parse_function_type<T>(stream: &mut State<T>) -> Result<Type, ParseError>
    where T: Iterator<Item = char>
{
    let left =
        parse_alt(
            |s| parse_parenthesized('(', ')', parse_type, s),
            |s| parse_alt(
                parse_parametric_type,
                |s| parse_alt(
                    parse_type_constant,
                    parse_type_variable,
                    s),
                s),
            stream)
        .map_err(|e| parse_error("parse_function_type: failed parsing left part", e))?;

    // println!("LEFT {}", left);

    skip_whitespace(stream)
    .map_err(|e| parse_error("parse_function_type: failed skipping whitespace before arrow", e))?;

    parse_string("->", stream)
    .map_err(|e| parse_error("parse_function_type: failed parsing \"->\"", e))?;

    skip_whitespace(stream)
    .map_err(|e| parse_error("parse_function_type: failed skipping whitespace after arrow", e))?;

    let right =
        parse_alt(
            |s| parse_parenthesized('(', ')', parse_type, s),
            parse_type,
            stream)
        .map_err(|e| parse_error("parse_function_type: failed parsing right part", e))?;

    Ok(t_fun(left, right))
}

pub fn parse_type_constant<T>(stream: &mut State<T>) -> Result<Type, ParseError>
where T: Iterator<Item = char>
{
    let name = parse_capitalized_identifier(stream)
        .map_err(|e| parse_error("parse_type_constant: failed", e))?;

    Ok(t_con(&name))
}

pub fn parse_type_variable<T>(stream: &mut State<T>) -> Result<Type, ParseError>
where T: Iterator<Item = char>
{
    let name = parse_uncapitalized_identifier(stream)
    .map_err(|e| parse_error("parse_type_variable: failed.", e))?;

    Ok(t_var_0(&name))
}

pub fn parse_parametric_type<T>(stream: &mut State<T>) -> Result<Type, ParseError>
where T: Iterator<Item = char>
{
    let name = parse_capitalized_identifier(stream)
        .map_err(|e| parse_error("parse_parametric_type: failed parsing type name.", e))?;

    fn parse_parameter<T>(stream: &mut State<T>) -> Result<Type, ParseError>
        where T: Iterator<Item = char>
    {
        let res =
            parse_alt(
                |s| parse_parenthesized('(', ')', parse_type, s),
                |s| parse_alt(
                    parse_type_variable,
                    parse_type_constant,
                    s),
                stream);

        skip_whitespace(stream)?;

        res
    }

    let params: Vec<Type> = parse_many(parse_parameter, stream)
        .map_err(|e| parse_error("parse_type_constant: failed parsing type parameters.", e))?;

    Ok(t_param(&name, &params))
}

pub fn parse_uncapitalized_identifier<T>(stream: &mut State<T>) -> Result<String, ParseError>
where T: Iterator<Item = char>
{
    let mut name : String = String::new();

    name.push(parse_predicate(|c| c.is_lowercase(), stream)
             .map_err(|e| parse_error("parse_uncapitalized_identifier: failed parsing first letter", e))?);
    name.extend(parse_many(|s|
        parse_predicate(|c| c.is_alphanumeric() || c == '_', s), stream)
             .map_err(|e| parse_error("parse_uncapitalized_identifier: failed parsing remaining letters", e))?);

    skip_whitespace(stream)?;
    
    if name.is_empty() {
        Err(parse_error_bottom("identifier is empty", stream))
    } else {
        Ok(name)
    }
}

pub fn parse_capitalized_identifier<T>(stream: &mut State<T>) -> Result<String, ParseError>
    where T: Iterator<Item = char>
{
    let mut name : String = String::new();

    name.push(parse_predicate(|c| c.is_uppercase(), stream)
             .map_err(|e| parse_error("parse_capitalized_identifier: failed parsing first letter", e))?);
    name.extend(parse_many(|s|
        parse_predicate(|c| c.is_alphanumeric() || c == '_', s), stream)
             .map_err(|e| parse_error("parse_capitalized_identifier: failed parsing remaining letters", e))?);

    skip_whitespace(stream)?;

    Ok(name)
}

pub fn skip_empty_lines<T>(stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>,
{
    parse_many(parse_empty_line, stream)
    .map_err(|e| parse_error("skip_empty_lines: failed.", e))?;

    Ok(())
}

pub fn parse_empty_line<T>(stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>
{
    skip_whitespace(stream)?;
    parse_char('\n', stream)
    .map_err(|e| parse_error("parse_empty_line: failed parsing newline character", e))
}

pub fn parse_line<T>(stream: &mut State<T>) -> Result<String, ParseError>
    where T: Iterator<Item = char>
{
    let line = parse_many( |s| parse_predicate(|c| c != '\n', s), stream)
    .map_err(|e| parse_error("parse_line: failed", e))
    .map(|cs| cs.into_iter().collect())?;

    // Skip optional newline character (may be absent if end of stream). Discard error.
    parse_char('\n', stream).ok();

    Ok(line)
}

pub fn parse_char<T>(c: char, stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>
{
    match stream.next() {
        None => Err(parse_error_bottom(
            &format!("Expected '{}' but reached end of stream.", c),
            stream )),
        Some(d) =>
            if d == c {
                Ok(())
            } else {
                Err(parse_error_bottom(
                    &format!("Expected '{}' but got '{}'", c, d),
                    stream))
            }
    }
}

pub fn parse_any_char<T>(stream: &mut State<T>) -> Result<char, ParseError>
    where T: Iterator<Item = char>
{
    match stream.next() {
        None => Err(parse_error_bottom(
            &format!("Expected any character but reached end of stream."),
            stream )),
        Some(d) => Ok(d),
    }
}

pub fn parse_whitespace<T>(stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>
{
    parse_predicate(|c| c.is_whitespace() && c != '\n', stream)
    .map_err(|e| parse_error("parse_whitespace: failed", e))?;

    Ok(())
}

pub fn parse_predicate<T, P>(p: P, stream: &mut State<T>) -> Result<char, ParseError>
where P: Fn(char) -> bool,
      T: Iterator<Item = char>
{
    match stream.next() {
        None => Err(parse_error_bottom(
            &format!("Expected character to be tested on a predicate but reached end of stream ({}:{}).",
                     stream.current_line, stream.current_col),
            stream)),
        Some(d) =>
            if p(d)  {
                Ok(d)
            } else {
                Err(parse_error_bottom(
                    &format!("Predicate unsatisfied for '{}' ({}:{})",
                                d, stream.current_line, stream.current_col),
                    stream))
            }
    }
}

pub fn parse_string<T>(s: &str, stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>
{
    for c in s.chars() {
        parse_char(c, stream)
        .map_err(|e| parse_error(
            &format!("parse_string: failed parsing string \"{}\".", s),
            e))?;
    }

    Ok(())
}

pub fn parse_parenthesized<T, P, U>(left: char, right: char, p: P, stream: &mut State<T>) -> Result<U, ParseError>
where T: Iterator<Item = char>,
      P: FnOnce(&mut State<T>) -> Result<U, ParseError>,
      U: Debug
{
    parse_char(left, stream)
    .map_err(|e| parse_error(&format!("parse_parenthesized: failed parsing {}", left), e))?;
    skip_whitespace(stream)?;

    let res = p(stream)
        .map_err(|e| parse_error("parse_parenthesized: failed parsing inside parentheses", e))?;

    skip_whitespace(stream)?;

    parse_char(right, stream)
    .map_err(|e| parse_error(&format!("parse_parenthesized: failed parsing {}", right), e))?;

    skip_whitespace(stream)?;

    Ok(res)
}

pub fn skip_whitespace<T>(stream: &mut State<T>) -> Result<(), ParseError>
where T: Iterator<Item = char>,
{
    parse_many(parse_whitespace, stream)
    .map_err(|e| parse_error("skip_whitespace: failed", e))?;

    Ok(())
}

pub fn parse_many<T, P, U>(p: P, stream: &mut State<T>) -> Result<Vec<U>, ParseError>
where T: Iterator<Item = char>,
      P: Fn(&mut State<T>) -> Result<U, ParseError>,
      //U: Debug
{
    let mut res = Vec::new();

    loop {
        match try_parse(&p, stream) {
            Ok(u) => {
                res.push(u);
                continue;
            }
            Err(_) => {
                break;
            }
        }
    }

    Ok(res)
}

pub fn parse_alt<T,P,Q,U>(p: P, q: Q, stream: &mut State<T>) -> Result<U, ParseError>
where T: Iterator<Item = char>,
      P: Fn(&mut State<T>) -> Result<U, ParseError>,
      Q: Fn(&mut State<T>) -> Result<U, ParseError>,
{
    match try_parse(p, stream) {
        Ok(u) => Ok(u),
        Err(_) => q(stream).map_err(|e| parse_error("parse_alt: no parser succeeded", e))
    }
}



pub fn try_parse<T, P, U>(p: P, stream: &mut State<T>) -> Result<U, ParseError>
    where T: Iterator<Item = char>,
          P: Fn(&mut State<T>) -> Result<U, ParseError>
{
    stream.checkpoint();

    let result = p(stream).map_err(|e| parse_error("try_parse: tried parser failed", e));

    if result.is_ok() {
        stream.forget();
    } else {
        stream.restore();
    }

    result
}

pub fn parse_end_of_stream<T>(stream: &mut State<T>) -> Result<(), ParseError>
    where T: Iterator<Item = char>,
{
    match stream.next() {
        Some(x) => Err(
            parse_error_bottom(
                &format!("parse_end_of_stream: expected end of stream but got '{}'", x),
            stream)),
        None => Ok(()),
    }
}

pub struct State<T>
where T: Iterator<Item = char>
{
    stream: T,
    buffer: Vec<char>,
    buf_pos: usize,
    checkpoints: Vec<usize>,
    current_line: usize,
    current_col: usize,
}


impl<T> fmt::Display for State<T>
where T: Iterator<Item = char>
{
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "State ({}, {}) buffer=[",
                          self.current_line, self.current_col)?;
                    for c in self.buffer.iter() {
                            write!(f, "'{}', ", c)?;
                    }
                    write!(f, "] buf_pos={} checkpoints=[", self.buf_pos)?;
                    for i in self.checkpoints.iter() {
                            write!(f, "{}, ", i)?;
                    }
                    write!(f, "]")?;

                    Ok(())
        }
}

pub fn state_from(s: &str) -> State<Chars> {
    State::new(s.chars())
}
    
impl<T> State<T>
where T: Iterator<Item = char>
{
    pub fn new(stream: T) -> State<T> {
        State {
            stream: stream,
            buffer: Vec::new(),
            buf_pos: 0,
            checkpoints: Vec::new(),
            current_line : 1,
            current_col : 1,
        }
    }

    pub fn checkpoint(&mut self) {
        self.checkpoints.push(self.buf_pos);
    }

    pub fn forget(&mut self) {
        self.checkpoints.pop();
    }

    pub fn restore(&mut self) {
        match self.checkpoints.pop() {
            None => panic!("No checkpoint to restore."),
            Some(x) => {
                self.current_line -= {
                    let sub = self.buffer[x..self.buf_pos].iter().filter(|c| **c == '\n').count();
                    self.buf_pos = x;
                    sub
                };
                //self.current_pos -=
            }
        }
    }
}

impl<T> Iterator for State<T>
where T: Iterator<Item = char>
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let next =
            if self.buf_pos < self.buffer.len() {
                self.buf_pos += 1;
                Some(self.buffer[self.buf_pos - 1])
            } else {
                let c = self.stream.next();
                if self.checkpoints.is_empty() {
                    self.buffer.clear();
                    self.buf_pos = 0;
                } else if c.is_some() {
                    self.buffer.push(c.unwrap().clone());
                    self.buf_pos += 1;
                }
                c
            };

        match next {
            Some(x) => {
                if x == '\n' {
                    self.current_line += 1;
                    self.current_col = 0;
                } else {
                    self.current_col += 1;
                }
            }
            None => (),
        }

        // println!("STREAM CURRENT ITEM {:?}", next);
        next
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_sy::{t_con, t_fun, t_var_0};

    #[test]
    fn test_parse_char() {
        let mut stream = state_from("blablabla.");
        assert!( parse_char('b', &mut stream).is_ok() );
        assert_eq!( stream.next(), Some('l') );

        let mut stream = state_from("blablabla.");
        assert!( parse_char('x', &mut stream).is_err());
    }


    #[test]
    fn test_skip_whitespace() {
        let mut stream = state_from("     ");
        assert!( skip_whitespace(&mut stream).is_ok() );
        assert_eq!(stream.next(), None);

        let mut stream = state_from("     a");
        assert!( skip_whitespace(&mut stream).is_ok() );
        assert_eq!(stream.next(), Some('a'));

        let mut stream = state_from("a    ");
        assert!( skip_whitespace(&mut stream).is_ok() );
        assert_eq!(stream.next(), Some('a'));
    }

    #[test]
    fn test_parse_string() {
        let mut stream = state_from("blablabla.");
        assert!( parse_string("bla", &mut stream).is_ok() );
        assert_eq!( stream.next(), Some('b') );

        let mut stream = state_from("blablabla.");
        assert!( parse_string("greu", &mut stream).is_err() );
    }

    #[test]
    fn test_parse_line() {
        let mut stream = state_from("blablabla.\ngreu");
        assert_eq!( parse_line(&mut stream), Ok(String::from("blablabla.")) );
        assert_eq!( stream.next(), Some('g') );

        let mut stream = state_from("blablabla.");
        assert_eq!( parse_line(&mut stream), Ok(String::from("blablabla.")) );
        assert_eq!( stream.next(), None );
    }

    #[test]
    fn test_parse_try() {
        let mut stream = state_from("bla.");
        assert_eq!(try_parse(|s| parse_char('b', s), &mut stream), Ok(()) );
        assert_eq!(stream.next(), Some('l'));

        let mut stream = state_from("bla.");
        assert!(try_parse(|s| parse_char('g', s), &mut stream).is_err() );
    }


    #[test]
    fn test_parse_many() {
        let mut stream = state_from("blablabla.");
        assert_eq!(
            parse_many(|s| parse_string("bla", s), &mut stream),
            Ok(vec![(), (), ()])
            );
        assert_eq!(stream.next(), Some('.'));
    }


    #[test]
    fn test_parse_alt() {
        let mut stream = state_from("bla.");
        assert!(
            parse_alt(|s| parse_string("bla", s),
                      |s| parse_string("greu", s),
                     &mut stream)
            .is_ok() );
        assert_eq!(stream.next(), Some('.'));

        let mut stream = state_from("greu.");
        assert!(
            parse_alt(|s| parse_string("bla", s),
                      |s| parse_string("greu", s),
                     &mut stream)
            .is_ok() );
        assert_eq!(stream.next(), Some('.'));

        let mut stream = state_from("arf.");
        assert!(
            parse_alt(|s| parse_string("bla", s),
                      |s| parse_string("greu", s),
                     &mut stream)
            .is_err() );
    }


    #[test]
    fn test_parse_parenthesized() {
        assert!(
            parse_parenthesized('(', ')', |s| parse_string("abc", s), &mut state_from("( abc )"))
            .is_ok());

        assert_eq!(
            parse_parenthesized('(', ')', 
                |s| parse_predicate(|c| c.is_alphanumeric(), s),
                &mut state_from("(a)")),
            Ok('a'));

        assert!(
            parse_parenthesized('(', ')', |s| parse_string("ab", s), &mut state_from("( abc )"))
            .is_err());
    }

    #[test]
    fn test_parse_cons_name() {
        assert_eq!(
            parse_cons_name(&mut state_from("abcd")),
            Ok(String::from("abcd")) );

        let mut stream = state_from("abcd: ");
        assert_eq!(
            parse_cons_name(&mut stream),
            Ok(String::from("abcd")) );
        assert_eq!( stream.next(), Some(':'));
    }

    #[test]
    fn test_parse_uncapitalized_identifier() {
        assert_eq!(
            parse_uncapitalized_identifier(&mut state_from("a")),
            Ok(String::from("a")) );

        assert_eq!(
            parse_uncapitalized_identifier(&mut state_from("bla")),
            Ok(String::from("bla")) );
    }

    #[test]
    fn test_parse_capitalized_identifier() {
        assert_eq!(
            parse_capitalized_identifier(&mut state_from("A")),
            Ok(String::from("A")) );

        assert_eq!(
            parse_capitalized_identifier(&mut state_from("Bla")),
            Ok(String::from("Bla")) );
    }

    #[test]
    fn test_parse_type_constant() {
        assert_eq!(
            parse_type_constant(&mut state_from("A")),
            Ok(t_con("A")) );

        assert_eq!(
            parse_type_constant(&mut state_from("Bla")),
            Ok(t_con("Bla")) );
    }

    #[test]
    fn test_parse_type_variable() {
        assert_eq!(
            parse_type_variable(&mut state_from("a")),
            Ok(t_var_0("a")) );

        assert_eq!(
            parse_type_variable(&mut state_from("bla")),
            Ok(t_var_0("bla")) );
    }

    #[test]
    fn test_parse_parametric_type() {
        assert_eq!(
            parse_parametric_type(&mut state_from("Bla a b")),
            Ok(t_param("Bla", &[t_var_0("a"), t_var_0("b")])) );

        assert_eq!(
            parse_parametric_type(&mut state_from("Bla (b)")),
            Ok(t_param("Bla", &[t_var_0("b")])) );

        assert_eq!(
            parse_parametric_type(&mut state_from("Bla A B")),
            Ok(t_param("Bla", &[t_con("A"), t_con("B")])) );

        assert_eq!(
            parse_parametric_type(&mut state_from("Bla (A a)")),
            Ok(t_param("Bla", &[t_param("A", &[t_var_0("a")])])) );
    }

    #[test]
    fn test_parse_function_type() {
        assert_eq!(
            parse_function_type(&mut state_from("a -> b")),
            Ok(t_fun(t_var_0("a"), t_var_0("b"))) );

        assert_eq!(
            parse_function_type(&mut state_from("A -> B")),
            Ok(t_fun(t_con("A"), t_con("B"))) );

        assert_eq!(
            parse_parenthesized('(', ')', parse_function_type, &mut state_from("(a -> b)")),
            Ok(t_fun(t_var_0("a"), t_var_0("b"))) );

        assert_eq!(
            parse_function_type(&mut state_from("a -> b -> c")),
            Ok(t_fun(t_var_0("a"), t_fun(t_var_0("b"), t_var_0("c")))) );
        
        assert_eq!(
            parse_function_type(&mut state_from("(a -> b) -> c")),
            Ok(t_fun(t_fun(t_var_0("a"), t_var_0("b")), t_var_0("c"))) );
    }
        

    #[test]
    fn test_parse_cons_declaration() {
        assert_eq!(
            parse_cons_declaration(&mut state_from("abcd: A")),
            Ok((String::from("abcd"), t_con("A"))) );

        assert_eq!(
            parse_cons_declaration(&mut state_from("abcd: a -> b")),
            Ok((String::from("abcd"), t_fun(t_var_0("a"), t_var_0("b")))) );
    }

    #[test]
    fn test_parse_cons_body() {
        assert_eq!(
            parse_cons_body(&mut state_from("> a")),
            Ok(Template(vec![TemplateBit::raw("a")])) );

        assert_eq!(
            parse_cons_body(&mut state_from("> {x}\n> {y}")),
            Ok(Template(vec![TemplateBit::key(0, "x")
                                , TemplateBit::raw("\n")
                                , TemplateBit::key(0, "y")])) );

        assert_eq!(
            parse_cons_body(&mut state_from("> {x}\n> {y}\n> {z}")),
            Ok(Template(vec![TemplateBit::key(0, "x")
                                , TemplateBit::raw("\n")
                                , TemplateBit::key(0, "y")
                                , TemplateBit::raw("\n")
                                , TemplateBit::key(0, "z")])) );
    }

    #[test]
    fn test_parse_cons_definition() {
        let input = "abcd\n> a";
        assert_eq!(
            parse_cons_definition(&mut state_from(input)),
            Ok((String::from("abcd"), vec![],
                Template(vec![TemplateBit::raw("a")]))) );

        let input = "f x y\n> {x}\n> {y}";
        assert_eq!(
            parse_cons_definition(&mut state_from(input)),
            Ok((String::from("f"), vec![String::from("x"), String::from("y")],
                Template(vec![TemplateBit::key(0, "x")
                                 , TemplateBit::raw("\n")
                                 , TemplateBit::key(0, "y")]))) );
    }

    #[test]
    fn test_parse_cons() {
        let input = "f: a -> b -> c\n\
                     f x y\n\
                     > {x}\n\
                     > {y}\n";
        assert_eq!(
            parse_cons(&mut state_from(input)),
            Ok((String::from("f"), t_fun(t_var_0("a"), t_fun(t_var_0("b"), t_var_0("c"))),
                    vec!["x".to_string(), "y".to_string()],
                    Template(vec![TemplateBit::key(0, "x")
                                     , TemplateBit::raw("\n")
                                     , TemplateBit::key(0, "y")
                                     , TemplateBit::raw("\n")])))
        );
    }

    #[test]
    fn test_parse_constructors() {
        let input = "abcd: A\n\
                     abcd\n\
                     > a\n\
                     \n\
                     f: a -> b -> c\n\
                     f x y\n\
                     > {x}\n\
                     > {y}";
        assert_eq!(
            parse_constructors(&mut state_from(input)),
            Ok([(String::from("abcd"), t_con("A"),
                    vec![],
                    Template(vec![TemplateBit::raw("a\n")])),
                (String::from("f"),  t_fun(t_var_0("a"), t_fun(t_var_0("b"), t_var_0("c"))),
                    vec!["x".to_string(), "y".to_string()],
                    Template(vec![TemplateBit::key(0, "x")
                                     , TemplateBit::raw("\n")
                                     , TemplateBit::key(0, "y")]))
               ].iter().cloned().collect())
            );
    }

    

    #[test]
    fn test_state_checkpoint() {
        // Checkpoints in sequence
        let input = "abcde";
        let mut s = State::new(input.chars());
        assert_eq!(s.next(), Some('a'));
        s.checkpoint();
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        s.restore();
        assert_eq!(s.next(), Some('b'));
        s.checkpoint();
        assert_eq!(s.next(), Some('c'));
        assert_eq!(s.next(), Some('d'));
        s.forget();
        assert_eq!(s.next(), Some('e'));
        assert_eq!(s.next(), None);

        // Nested checkpoints
        let input = "abcde";
        let mut s = State::new(input.chars());
        s.checkpoint();
        assert_eq!(s.next(), Some('a'));
        s.checkpoint();
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        s.restore();
        assert_eq!(s.next(), Some('b'));
        s.restore();
        assert_eq!(s.next(), Some('a'));
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        assert_eq!(s.next(), Some('d'));
        assert_eq!(s.next(), Some('e'));
        assert_eq!(s.next(), None);

        // Forget nested checkpoints
        let input = "abcde";
        let mut s = State::new(input.chars());
        s.checkpoint();
        assert_eq!(s.next(), Some('a'));
        s.checkpoint();
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        s.forget();
        assert_eq!(s.next(), Some('d'));
        s.restore();
        assert_eq!(s.next(), Some('a'));
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        assert_eq!(s.next(), Some('d'));
        assert_eq!(s.next(), Some('e'));
        assert_eq!(s.next(), None);

        // Restore after reaching end of stream
        let input = "abcde";
        let mut s = State::new(input.chars());
        s.checkpoint();
        assert_eq!(s.next(), Some('a'));
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        assert_eq!(s.next(), Some('d'));
        assert_eq!(s.next(), Some('e'));
        assert_eq!(s.next(), None);
        s.restore();
        assert_eq!(s.next(), Some('a'));
        assert_eq!(s.next(), Some('b'));
        assert_eq!(s.next(), Some('c'));
        assert_eq!(s.next(), Some('d'));
        assert_eq!(s.next(), Some('e'));
        assert_eq!(s.next(), None);
    }
}
