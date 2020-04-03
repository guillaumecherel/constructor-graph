#![allow(dead_code)]

use std::fmt;
use std::iter;

use crate::type_sy::{VarNames, Type, var_names, arity};
use crate::type_sy::{t_var_0, t_fun, t_fun_seq, t_con};

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Hash)]
pub enum Cons {
    Id, // Identity constructor
    Data(usize), // User defined constructor
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
        Ap => write!(f, "&"),
        Comp => write!(f, "<"),
        Pair(a, b) => write!(f, "({}, {})", a, b),
    }
  }
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

    let mut args_types = vec![];
    let mut cur_type = t;
    let mut fun_types = cur_type.fun_split();

    while fun_types.is_some() {
        let (src, tgt) = fun_types.unwrap();
        args_types.push(src.clone());
        cur_type = tgt;
        fun_types = cur_type.fun_split();
    }

    let ret_source = t_fun(cur_type.clone(), new_var.clone());

    args_types.push(new_var);
    let ret_target = t_fun_seq(&args_types);

    let ret_type = t_fun(ret_source, ret_target);

    (c, ret_type)
}

pub fn cat_cons(xs: Vec<(String, Type)>) -> Vec<(String, Cons, Type)> {
    (0..).zip(xs.iter()).map(
        |(i ,(n, t))| match using(Data(i), t) { (c_, t_) => (String::from(n), c_, t_)})
    .collect()
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

pub fn script_cons(c: &Cons, cons_def: &Vec<(String, Type)>) -> String {
    //println!("SCRIPT_CONS {}", c);
    // match Pair(f, x)
    run_pair(c, run_any, run_any,
        |f, g| format!("{}\n{}",
            script_cons(f, cons_def),
            indent(2, &script_cons(g, cons_def))))
    // match Data(i)
    .or_else( || run_data(c, |&i| format!("{}", cons_def[i].0)) )
    .expect(&format!("I don't know how to write script for {}", &c))
}

fn indent(width: usize, txt: &str) -> String {
    let indent: String = iter::repeat(" ").take(width).collect();
    let mut lines = txt.lines();
    let mut result: String = lines.next().map(|l| String::from(&indent) + l).unwrap_or("".to_string()).to_string();

    for l in lines {
        result.push_str("\n");
        result.push_str(&indent);
        result.push_str(l);
    }

    result
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
