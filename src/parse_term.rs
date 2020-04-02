
// pub fn parse_terms<T>(stream: &mut T) -> Result<VecDeque<Term>, String>
//     where T: Iterator<Item = char>,
// {
//     let term = parse_term(stream)?;
//     parse_empty_lines(stream)?;
// 
//     match stream.peekable().peek() {
//        None => Ok([term].into_iter().cloned().collect()),
//        Some(_) => {
//            let terms = parse_terms(stream)?;
//            terms.push_front(term);
//            Ok(terms)
//        }
//     }
// }
// 
// pub fn parse_empty_lines<T>(stream: &mut T) -> Result<(), String>
//     where T: Iterator<Item = char>,
// {
//     match try_parse(parse_empty_line, &mut stream) {
//         Err(_) => {
//             Ok(())
//         }
//         Ok(_) =>
//             match stream.peekable().peek() {
//                None => Ok(()),
//                Some(_) => parse_empty_line(stream),
//             },
//     }
// }
// 
// pub fn parse_empty_line<T>(stream: &mut T) -> Result<(), String>
//     where T: Iterator<Item = char>
// {
//     stream.skip_while(|c| c.is_whitespace() && *c != '\n' );
//     match stream.next() {
//        None => Ok(()),
//        Some('\n') => Ok(()),
//        Some(c) => Err(format!("Expected whitespace but found {}", c)),
//     }
// }
// 
// pub fn parse_term<T>(stream: &mut T) -> Result<Term, String>
//     where T: Iterator<Item = char>
// {
//     let name = parse_term_name(stream)?;
//     parse_char(':', stream)?;
//     let t = parse_type(stream)?;
//     Ok(Term(name, t))
// }
// 
// pub fn parse_term_name<T>(stream: &mut T) -> Result<String, String>
//     where T: Iterator<Item = char>
// {
//     let name : String = stream.take_while(|c| c.is_alphanumeric() || *c == '_').collect();
//     stream.skip_while(|c| c.is_whitespace());
//     if name.is_empty() {
//         Err(String::from("Term name is empty"))
//     } else {
//         Ok(name)
//     }
// }
// 
// pub fn parse_type<T>(stream: &mut T) -> Result<Type, String>
//     where T: Iterator<Item = char>
// {
//     try_parse(parse_function_type, &mut stream)
//     .or(try_parse(parse_parametric_type, &mut stream))
//     .or(try_parse(parse_type_constant, &mut stream))
//     .or(try_parse(parse_type_variable, &mut stream))
// }
// 
// pub fn parse_function_type<T>(stream: &mut T) -> Result<Type, String>
//     where T: Iterator<Item = char>
// {
//     let left = try_parse(|s| parse_parenthesized(parse_type, &mut s), &mut stream)
//                .or(try_parse(parse_parametric_type, &mut stream))
//                .or(try_parse(parse_type_constant, &mut stream))
//                .or(try_parse(parse_type_variable, &mut stream))?;
// 
//     parse_string("->", &mut stream)?;
// 
//     stream.skip_while(|c| c.is_whitespace());
// 
//     let right = try_parse(|s| parse_parenthesized(parse_type, &mut s), &mut stream)
//                 .or(parse_type(&mut stream))?;
// 
//     Ok(t_fun(left, right))
// }
// 
// 
// pub fn parse_type_constant<T>(stream: &mut T) -> Result<Type, String>
//     where T: Iterator<Item = char>
// {
//     let mut name : String = String::new();
// 
//     match stream.next() {
//         None => Err(String::from("Expected an uppercase letter while parsing type constante, but reached end of stream")),
//         Some(c) => if c.is_uppercase() {
//             name.push(c);
//             Ok(())
//         } else {
//             Err(format!("Expected an uppercase letter while parsing a type constant, but got {}", c))
//         }
//     }?;
// 
//     name.extend(stream.take_while(|c| c.is_alphanumeric() || *c == '_'));
// 
//     stream.skip_while(|c| c.is_whitespace());
// 
//     Ok(t_con(&name))
// }
// 
// pub fn parse_type_variable<T>(stream: &mut T) -> Result<Type, String>
//     where T: Iterator<Item = char>
// {
//     let mut name : String = String::new();
// 
//     match stream.next() {
//         None => Err(String::from("Expected a lowercase letter while parsing type variable, but reached end of stream")),
//         Some(c) => if c.is_lowercase() {
//             name.push(c);
//             Ok(())
//         } else {
//             Err(format!("Expected an lowercase letter while parsing a type variable, but got {}", c))
//         }
//     }?;
// 
//     name.extend(stream.take_while(|c| c.is_alphanumeric() || *c == '_'));
// 
//     stream.skip_while(|c| c.is_whitespace());
// 
//     Ok(t_var_0(&name))
// }
// 
// pub fn parse_parametric_type<T>(stream: &mut T) -> Result<Type, String>
//     where T: Iterator<Item = char>
// {
//     let mut name : String = String::new();
// 
//     match stream.next() {
//         None => Err(String::from("Expected an uppercase letter while parsing parametric type, but reached end of stream")),
//         Some(c) => if c.is_uppercase() {
//             name.push(c);
//             Ok(())
//         } else {
//             Err(format!("Expected an uppercase letter while parsing a parametric type, but got {}", c))
//         }
//     }?;
// 
//     name.extend(stream.take_while(|c| c.is_alphanumeric() || *c == '_'));
// 
//     stream.skip_while(|c| c.is_whitespace());
// 
//     fn parse_parameter<T>(stream: &mut T) -> Result<Type, String>
//         where T: Iterator<Item = char>
//     {
//         let res = try_parse(|s| parse_parenthesized(parse_type, &mut s), &mut stream)
//         .or(try_parse(parse_type_constant, &mut stream))
//         .or(try_parse(parse_type_variable, &mut stream));
// 
//         stream.skip_while(|c| c.is_whitespace());
// 
//         res
//     }
// 
//     let params: Vec<Type> = iter::from_fn(|| try_parse(parse_parameter, &mut stream).ok()).collect();
// 
//     Ok(t_param(&name, &params))
// }
// 
// pub fn parse_char<T>(c: char, stream: &mut T) -> Result<(), String>
//     where T: Iterator<Item = char>
// {
//     match stream.next() {
//         None => Err(String::from("Expected ':' but reached end of stream.")),
//         Some(d) => if d == c {
//             stream.skip_while(|c| c.is_whitespace());
//             Ok(())
//         } else {
//             Err(format!("Expected ':' but got '{}'", d))
//         }
//     }
// }
// 
// pub fn parse_string<T>(s: &str, stream: &mut T) -> Result<(), String>
//     where T: Iterator<Item = char>
// {
//     match stream.next() {
//         None => Err(String::from("Expected ':' but reached end of stream.")),
//         Some(d) => if d != s.chars().next().unwrap() {
//             Err(format!("Expected '{}' but got '{}' when trying to parse string \"{}\"", s.chars().next().unwrap(), d, s))
//         } else {
//             parse_string(&s[1..], stream)?;
//             stream.skip_while(|c| c.is_whitespace());
//             Ok(())
//         }
//     }
// }
// 
// pub fn parse_parenthesized<T, P, U>(p: P, stream: &mut T) -> Result<U, String>
//     where T: Iterator<Item = char>,
//           P: FnMut(&mut T) -> Result<U, String>
// {
//     parse_char('(', stream)?;
//     stream.skip_while(|c| c.is_whitespace());
// 
//     let res = p(stream);
// 
//     parse_char(')', stream);
//     stream.skip_while(|c| c.is_whitespace());
// 
//     res
// }
// 
// pub fn try_parse<T, P, U>(p: P, stream: &mut T) -> Result<U, String>
//     where T: Iterator<Item = char>,
//           P: FnMut(T) -> Result<U, String>
// {
//     let checkpoint = stream.clone();
// 
//     match p(stream) {
//         Err(_) => stream = checkpoint,
//         r => r
//     }
// }


