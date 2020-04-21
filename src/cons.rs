#![allow(dead_code)]

use std::fmt;
use std::io;
use std::io::Write;
use std::collections::HashSet;

use crate::type_sy::{VarNames, Type, var_names, arity, mgu, distinguish};
use crate::type_sy::{t_var_0, t_fun, t_fun_seq, t_con, t_int, t_double};
use crate::util;
use crate::template::{Template, TemplateBit};

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Hash)]
pub enum Cons {
    Id, // Identity constructor
    Data(usize), // User defined constructor
    Special(SpecialCons), // Constructor triggering actions
    Value(String), // Constructor for a simple value
    Ap, // Application constructor
    Comp, // Composition constructor
    Pair(Box<Cons>, Box<Cons>), //Application of a constructor to another
}

pub fn pair(a: Cons, b: Cons) -> Cons { Pair(Box::new(a), Box::new(b)) }

use Cons::*;

fn run_id(x: &Cons) -> Option<()>
{
    match x {
        Id => Some(()),
        _ => None,
    }
}

fn run_data<'a, F, T>(x: &'a Cons, f: F) -> Option<T>
where F: FnOnce(&'a usize) -> T
{
    match x {
        Data(i) => Some(f(i)),
        _ => None,
    }
}

fn run_special<'a, F, T>(x: &'a Cons, f: F) -> Option<T>
where F: FnOnce(&'a SpecialCons) -> T
{
    match x {
        Special(i) => Some(f(i)),
        _ => None,
    }
}

fn run_value<'a, F, T>(x: &'a Cons, f: F) -> Option<T>
where F: FnOnce(&'a String) -> T
{
    match x {
        Value(i) => Some(f(i)),
        _ => None,
    }
}

fn run_ap(x: &Cons) -> Option<()>
{
    match x {
        Ap => Some(()),
        _ => None,
    }
}

fn run_comp(x: &Cons) -> Option<()>
{
    match x {
        Comp => Some(()),
        _ => None,
    }
}

fn run_pair<'a, F, G, H, T, U, V>(x: &'a Cons, f: F, g: G, h: H) -> Option<V>
where F: FnOnce(&'a Cons) -> Option<T>,
      G: FnOnce(&'a Cons) -> Option<U>,
      H: FnOnce(T, U) -> V,
{
    match x {
        Pair(a, b) =>
            match (f(&*a), g(&*b)) {
                (Some(fa), Some(fb)) => Some(h(fa, fb)),
                _ => None,
            }
        _ => None,
    }
}

fn run_any(x: &Cons) -> Option<&Cons>
{
    Some(x)
}

impl fmt::Display for Cons {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
        Data(a) => write!(f, "{:?}", a),
        Id => write!(f, "Id"),
        Special(c) => write!(f, "Special {:?}", c),
        Value(s) => write!(f, "Value {}", s),
        Ap => write!(f, "&"),
        Comp => write!(f, "<"),
        Pair(a, b) => write!(f, "({}, {})", a, b),
    }
  }
}

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Hash)]
pub enum SpecialCons {
    ReadText,
    ReadInt,
    ReadDouble,
    ReadFilePath,
}

impl SpecialCons {
    pub fn run(&self) -> Cons {
        match self {
            SpecialCons::ReadText => {
                loop {
                    print!("Reading Text> ");
                    io::stdout().flush().unwrap();
                    let mut input = String::new();
                    match io::stdin().read_line(&mut input) {
                        Err(_) => {
                            println!("Failed to read line.");
                            continue
                        }
                        Ok(_) => {
                            let trimmed = input.trim();
                            break Value(trimmed.to_string())
                        }
                    };
                }
            }
            SpecialCons::ReadInt => {
                loop {
                    print!("Reading Int> ");
                    io::stdout().flush().unwrap();
                    let mut input = String::new();
                    match io::stdin().read_line(&mut input) {
                        Err(_) => {
                            println!("Failed to read line.");
                            continue
                        }
                        Ok(_) => {
                            let trimmed = input.trim();
                            match trimmed.parse::<usize>() {
                                Err(_) => {
                                    println!("Expecting an integer.");
                                    continue
                                },
                                Ok(_) => {
                                    break Value(trimmed.to_string())
                                }
                            }
                        }
                    };
                }
            }
            SpecialCons::ReadDouble => {
                loop {
                    print!("Reading Double> ");
                    io::stdout().flush().unwrap();
                    let mut input = String::new();
                    match io::stdin().read_line(&mut input) {
                        Err(_) => {
                            println!("Failed to read line.");
                            continue
                        }
                        Ok(_) =>
                            match input.trim().parse::<f64>() {
                                Err(_) => {
                                    println!("Expecting an double.");
                                    continue
                                }
                                Ok(_) => {
                                    let trimmed = input.trim();
                                    break Value(trimmed.to_string())
                                }
                            }
                    };
                }
            }
            SpecialCons::ReadFilePath => {
                loop {
                    print!("Reading Path> ");
                    io::stdout().flush().unwrap();
                    let mut input = String::new();
                    match io::stdin().read_line(&mut input) {
                        Err(_) => {
                            println!("Failed to read line.");
                            continue
                        }
                        Ok(_) => {
                            let trimmed = input.trim();
                            break Value(trimmed.to_string())
                        }
                    };
                }
            }
        }
    }
}

pub fn predef_cons() -> Vec<(String, Cons, Type, Vec<String>)> {
    vec![
        (String::from("read_int"), Special(SpecialCons::ReadInt), t_int(), vec![]),
        (String::from("read_double"), Special(SpecialCons::ReadDouble), t_double(), vec![]),
        (String::from("read_text"), Special(SpecialCons::ReadText), t_con("Text"), vec![]),
        (String::from("read_file_path"), Special(SpecialCons::ReadFilePath), t_con("FilePath"), vec![]),
    ]
}

// Returns a constructors of type (a -> b) -> (a1 -> a2 -> ... -> an -> b)
// given x of type a1 -> ... -> an -> a. x is nullary of type a, then returns a
// constructor of type (a -> b) -> b.
fn using(x: Cons, t: &Type) -> (Cons, Type) {
    let arit = arity(t);
    let mut c = Pair(Box::new(Ap), Box::new(x));

    for _i in 0..arit {
        c = Pair(Box::new(Pair(Box::new(Comp), Box::new(c))), Box::new(Comp));
    }

    let mut candidates = VarNames::excluding(var_names(t).into_iter());
    let new_var = t_var_0(&candidates.next().expect("No available var name."));

    let (mut args_types, cur_type) = t.split();
    
    let res_source = t_fun(cur_type.clone(), new_var.clone());

    args_types.push(&new_var);
    let res_target = t_fun_seq(&args_types.into_iter().cloned().collect::<Vec<Type>>());

    let res_type = t_fun(res_source, res_target);

    (c, res_type)
}

pub fn cat_cons(xs: Vec<(String, Cons, Type)>) -> Vec<(String, Cons, Type)> {
    xs.iter().map(
        |(n, c, t)| match using(c.clone(), t) { (c_, t_) => (String::from(n), c_, t_)})
    .collect()
}

// Performs the actions triggered by special constructors
pub fn run_special_cons(cons: &Cons) -> Cons {
    run_special(cons, |sp| sp.run())
    .or_else(||
        run_pair(cons,
            |l| Some(run_special_cons(l)),
            |r| Some(run_special_cons(r)),
            |d, e| pair(d, e))
    )
    .or_else(|| Some(cons.clone()))
    .unwrap()
}

// Interpret constructors Comp, Ap and Pair to leave only user defined constructors:
// (((Comp, f), g), x) -> uncat_cons(f, (g, x))
// ((Ap, x), f) -> uncat_cons(f, x)
// (f, g) -> uncat_cons(uncat_cons(f), uncat_cons(g))
// Data(x) -> Data(x)
pub fn uncat_cons(cons: &Cons) -> Cons {
    // match Pair(Pair(Pair(Comp, c), d), e)
    run_pair(cons,
        |l| run_pair(l,
            |ll| run_pair(ll, run_comp, run_any, |_, llr| llr),
            run_any,
            |a, b| (a,b)),
        run_any,
        |(c, d), e| {
            // println!("Reducing Comp {}", cons);
            uncat_cons(
            &Pair(Box::new(uncat_cons(c)),
                 Box::new(
                     uncat_cons(&Pair(
                         Box::new(uncat_cons(d)),
                         Box::new(uncat_cons(e)))))))
        })
    // // match Pair(Pair(Comp, Pair(Ap, x)), f)
    // .or_else(
    //     || run_pair(cons,
    //         |l| run_pair(l,
    //             run_comp,
    //             |lr| run_pair(lr, run_ap, run_any, |_, x| x),
    //             |_, x| x),
    //         run_any,
    //         |x, f| {
    //             // println!("Reducing Comp Ap x f {}", cons);
    //             uncat_cons(&pair(uncat_cons(f), uncat_cons(x)))
    //         })
    // )
    // match Pair(Pair(Comp, Id), d)
    // .or_else(
    //     || run_pair(cons,
    //         |l| run_pair(l, run_comp, run_id, |_, _| ()),
    //         run_any,
    //         |_, d| {
    //             // println!("Reducing Comp Id x {}", cons);
    //             uncat_cons(d)
    //         })
    // )
    // // match Pair(Pair(Comp, d), Id)
    // .or_else(
    //     || run_pair(cons,
    //         |l| run_pair(l, run_comp, run_any, |_, d| d),
    //         run_id,
    //         |d, _| {
    //             // println!("Reducing Comp x Id {}", cons);
    //             uncat_cons(d)
    //         })
    // )
    // match Pair(Pair(Ap, d), e)
    .or_else(
        || run_pair(cons,
           |l| run_pair(l, run_ap, run_any, |_, lr| lr),
           run_any,
           |d, e| {
                // println!("Reducing Ap {}", cons);
                uncat_cons(&Pair(Box::new(uncat_cons(e)), Box::new(uncat_cons(d))))
           })
    )
    // match Pair(Id, x)
    .or_else(
        || run_pair(cons, run_id, run_any,
            |_, x| {
                // println!("Reducing Id {}", cons);
                uncat_cons(x)
            })
    )
    // // match Pair(Comp, Id)
    // .or_else(
    //     || run_pair(cons, run_comp, run_id,
    //         |_, _| {
    //             // println!("Reducing Comp Id {}", cons);
    //             Id
    //         })
    // )
    // match Pair(f, g)
    .or_else(
        || run_pair(cons, run_any, run_any,
           |f, g| {
               // println!("Reducing Pair {}", cons);
               Pair(Box::new(uncat_cons(f)), Box::new(uncat_cons(g)))
           })
    )
    // match Data(x), Comp, Ap
    .or_else(|| Some(cons.clone()))
    .unwrap()
}

pub fn script_cons(c: &Cons, cons_def: &Vec<(String, Cons, Type)>) -> String {
    println!("SCRIPT_CONS {}", c);
    // match Pair(f, x)
    run_pair(c, run_any, run_any,
        |f, g| format!("{}\n{}",
            script_cons(f, cons_def),
            util::indent(2, &script_cons(g, cons_def), false)))
    // match Data(i)
    .or_else( || run_data(c, |&i| format!("{}", cons_def[i].0)) )
    // match Value(s)
    .or_else( || run_value(c, |s| s.clone()) )
    .expect(&format!("I don't know how to write script for {}", &c))
}

pub fn script_template(c: &Cons, cons_def: &Vec<(String, Cons, Type, Vec<String>, Template)>) -> Result<String, String> {

    pub fn go(c: &Cons, cons_def: &Vec<(String, Cons, Type, Vec<String>, Template)>) -> (Vec<String>, Template) {
        // match Pair(f, x)
        run_pair(c, run_any, run_any,
            |f, g| {
                let (args, mut body) = go(f, cons_def);
                let (args_g, body_g) = go(g, cons_def);

                if !args_g.is_empty() {
                    panic!("Free arguments remain in {}", g);
                }

                // replace any occurence of args[0] in body by body_g
                match args.split_first() {
                    Some((arg0, args_left)) => {
                        body.replace(&arg0, &body_g.to_string().unwrap());
                        (args_left.to_owned(), body)
                    }
                    None => panic!("No more free argument in {} while appling to {}", f, &body_g.to_string().unwrap()),
                }
        })
        // match Data(i)
        .or_else( || run_data(c, |&i| (cons_def[i].3.clone(), cons_def[i].4.clone())) )
        // match Value(s)
        .or_else( || run_value(c, |s| (Vec::new(), Template(vec![TemplateBit::raw(s)]))) )
        .expect(&format!("I don't know how to write script for {}", &c))
    }

    let (_, template) = go(c, cons_def);

    template.to_string()
}

//Returns a list of types for which no constructor was found
pub fn list_no_cons<'a>(cons: &'a[(String, Cons, Type)]) -> Vec<(&'a String, &'a Type)> {
    let mut input_types = HashSet::new();
    let mut output_types = HashSet::new();

    for (n, _, t) in cons {
        let (args, out) = t.split();
        output_types.insert(out);
        for a in args.into_iter() {
            input_types.insert((a, n));
        }
    }

    // keep all types in input_types that unify with no type of output_typese.
    input_types.into_iter()
    .filter(|(it,_)| output_types.iter().all(|ot| {
        let (itd, otd) = distinguish(it, ot);
        mgu(&itd, &otd).is_err()
    }))
    .map(|(it, n)| (n, it))
    .collect()
}

pub fn cons_test() -> Vec<(String, Type)> {
    vec![
        // A: A
        (String::from("ConsA"), t_con("A")),
        // B: A -> B
        (String::from("ConsB"), t_fun(t_con("A"), t_con("B"))),
        (String::from("go"), t_fun(t_con("B"), t_con("SCRIPT"))),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_using() {

        // The function using should return the constructor (Ap, x): (A -> a) -> a
        // given the constructor x: A,
        let expected_cons = pair(Ap, Data(0));
        let expected_type = t_fun(t_fun(t_con("A"), t_var_0("a")), t_var_0("a"));
        assert_eq!(
            using(Data(0), &t_con("A")),
            (expected_cons, expected_type),
        );

        // The function using should return the constructor
        // ((Comp, (Ap, x)), Comp): (B -> a) -> (A -> B)
        // given the constructor x: A -> B,
        let expected_cons = pair(pair(Comp, pair(Ap, Data(0))), Comp);
        let expected_type = t_fun(t_fun(t_con("B"), t_var_0("a")), t_fun(t_con("A"), t_var_0("a")));
        assert_eq!(
            using(Data(0), &t_fun(t_con("A"), t_con("B"))),
            (expected_cons, expected_type),
        );
    }

    #[test]
    fn test_uncat_cons() {
        let x = || Data(0);
        let f = || Data(1);
        let g = || Data(2);
        let comp_f_g = || pair(pair(Comp, f()), g());
        let ap_x = || pair(Ap, x());

        // ((Ap, x), f) = (f, x)
        assert_eq!(
            uncat_cons(&pair(ap_x(), f())),
            pair(f(), x())
        );

        // (((Comp, f), g), x) = (f, (g ,x))
        assert_eq!(
            uncat_cons(&pair(comp_f_g(), x())),
            pair(f(), pair(g(), x()))
        );

        // let go: SCRIPT
        // ((&, go), Id) = go
        let go = || Data(0);
        assert_eq!(
            uncat_cons(&pair(pair(Ap, go()), Id)),
            go(),
        );

        // let go: A -> Script
        //     a: A
        // check (&a . &go . <) id == go a
        // (&a . &go . <) = ((Comp, (Ap, a)), ((Comp, (Ap, go)), Comp))
        let go = || Data(0);
        let a = || Data(1);
        assert_eq!(
            uncat_cons(
                &pair(pair(pair(Comp, pair(Ap, a())),
                           pair(pair(Comp, pair(Ap, go())), Comp)),
                      Id)),
            pair(go(), a()),
        );
    }
}
