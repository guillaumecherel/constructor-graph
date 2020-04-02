#![allow(dead_code)]

use std::collections::VecDeque;
use std::iter::Iterator;
use std::fmt;

use crate::cons::{Cons};
use crate::type_sy::{mgu, VarNames, Type, var_names, fresh_inst, Tyvar, Subst, Scheme, Types, quantify};
use crate::type_sy::{t_fun};


//// Morphisms
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Clone)]
#[derive(Debug)]
#[derive(Hash)]
pub struct Morphism {
  pub name: String,
  pub cons: Cons,
  pub source: Type,
  pub target: Type,
}

impl Morphism {
    pub fn new(name: &str, cons: Cons, source: Type, target: Type) -> Morphism {
        Morphism {
            name : String::from(name),
            cons : cons,
            source : source,
            target : target,
        }
    }

    // Morphism composition operator: given self: X -> Y and m: Y -> Z, self.compose(m) : X -> Z.
    pub fn and_then(&self, m: &Morphism) -> Result<Morphism, String> {
        let mut vn = VarNames::excluding(
            var_names(&self.source).into_iter()
            .chain(var_names(&self.target).into_iter())
        );
        let q = quantify(None, &t_fun(m.source.clone(), m.target.clone()));
        let i = fresh_inst(&q, &mut vn);
        mgu(&self.target, &i.fun_source().unwrap()).map(|u| {
            Morphism::new(
                &(m.name.to_owned() + "." + &self.name),
                Cons::Pair(
                    Box::new(Cons::Pair(
                        Box::new(Cons::Comp),
                        Box::new(m.cons.clone()))),
                    Box::new(self.cons.clone())),
                self.source.apply_substitution(&u),
                i.fun_target().unwrap().apply_substitution(&u),
            )
        })
    }
}

impl fmt::Display for Morphism {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
     write!(f, "Morphism {}: {} --> {} = {}", self.name, self.source, self.target, self.cons)
  }
}

// Morphisms having the given source type.
pub fn morphisms_from_source(source: &Type, mss: &Vec<MorphScheme>) -> Vec<Morphism> {
    mss.iter().filter_map(|ms: &MorphScheme| -> Option<Morphism> {
        ms.inst_ap(source).ok()
    }).collect()
}

// Iterator listing the morphisms starting from the given sources and exploring the
// induced graph in a breadth first way.
pub fn morphisms_bf(sources: &Vec<&Type>, mss: &Vec<MorphScheme>) -> MorphismsBF {
    let q = sources.iter().flat_map(|t| morphisms_from_source(t, mss)).collect();
    MorphismsBF {
        queue: q,
        morph_schemes: mss.clone(),
    }
}

pub struct MorphismsBF {
    pub queue: VecDeque<Morphism>,
    pub morph_schemes: Vec<MorphScheme>,
}

impl Iterator for MorphismsBF {
    type Item = Morphism;

    fn next(&mut self) -> Option<Self::Item> {
        match self.queue.pop_front() {
            None => None,
            Some(m) => {
                let next = morphisms_from_source(&m.target, &self.morph_schemes);
                self.queue.extend(next.into_iter());
                Some(m)
            }
        }
    }
}



//// MorphSchemes: Type machinery to instantiate morphisms from a given source type.

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Clone)]
#[derive(Debug)]
pub struct MorphScheme {
  name: String,
  cons: Cons,
  scheme: Scheme,
}

impl MorphScheme {
    fn new(name: &str, cons: Cons, source: Type, target: Type) -> MorphScheme {
        let f = t_fun(source, target);
        MorphScheme {
            name : String::from(name),
            cons : cons,
            scheme : quantify(None,&f),
        }
    }

    // Return None if t is not a function type (TAp)
    fn from_type(name: &str, cons: Cons, t: &Type) -> Option<MorphScheme> {
        match t {
             Type::TAp(_, _) => {
                 let s : Scheme = quantify(None, &t);
                 Some(MorphScheme {
                         name: String::from(name),
                         cons: cons,
                         scheme: s,
                 })
             },
             _ => None,
       }
    }

    fn source(&self) -> Scheme {
       match &self.scheme.t {
           Type::TAp(s, _) =>
               Scheme{
                   kinds: self.scheme.kinds.clone(),
                   t: *s.clone()
               },
           _ => panic!("MorphSchemes underlying Scheme should be a function type TAp."),
       }
    }

    fn target(&self) -> Scheme {
       match &self.scheme.t {
           Type::TAp(_, t) =>
               Scheme{
                   kinds: self.scheme.kinds.clone(),
                   t: *t.clone()
               },
           _ => panic!("MorphSchemes underlying Scheme should be a function type TAp.")
       }
    }

    // Forward composition: given self: X -> Y and m: Y -> Z, self.compose(m) : X -> Z.
    fn and_then(&self, m: &MorphScheme) -> Result<MorphScheme, String> {
        let mut vn = VarNames::excluding(
            var_names(&self.scheme).into_iter()
            .chain(var_names(&m.scheme).into_iter())
         );
        let si = fresh_inst(&self.scheme, &mut vn);
        let mi = fresh_inst(&m.scheme, &mut vn);
        mgu(&si.fun_target().unwrap(), &mi.fun_source().unwrap()).map(|u| {
            MorphScheme::new(
                &(m.name.to_owned()  + "." + &self.name),
                Cons::Pair(
                    Box::new(Cons::Pair(
                        Box::new(Cons::Comp),
                        Box::new(m.cons.clone()))),
                    Box::new(self.cons.clone())),
                si.fun_source().unwrap().apply_substitution(&u),
                mi.fun_target().unwrap().apply_substitution(&u),
            )
        })
    }

    // Return the morphism that resuls from applying arg to the function represented
    // by self. Creates a fresh instance i of self avoiding any type variable name clash
    // with the argument by excluding from the new variable name any name that appears in arg,
    // then computes s = (mgu i.fun_source() arg) and applies it to both i.fun_source() and i.fun_target().
    // Return None if the mgu does not exist.
    fn inst_ap(&self, arg: &Type) -> Result<Morphism, String> {
        let mut vn = VarNames::excluding(var_names(arg).into_iter());
        let i = fresh_inst(&self.scheme, &mut vn);
        let i_source = i.fun_source().ok_or(String::from("Not a function"))?;
        mgu(&i_source, arg).map(|u| {
            Morphism::new(
                &self.name,
                self.cons.clone(),
                i_source.apply_substitution(&u),
                i.fun_target().unwrap().apply_substitution(&u),
            )
        })
    }
}

impl Types for MorphScheme {
    fn apply_substitution(&self, substitution: &Subst) -> MorphScheme {
       MorphScheme {
           name: self.name.clone(),
           cons: self.cons.clone(),
           scheme: self.scheme.apply_substitution(substitution),
       }
    }

    fn tv(&self) -> VecDeque<&Tyvar> {
       self.scheme.tv()
    }
}
    
impl fmt::Display for MorphScheme {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      MorphScheme{name, cons, scheme} => write!(f, "{}: {} = {} ", name, scheme, cons),
    }
  }
}

pub fn morph_schemes_from_cons(cons: &Vec<(String, Cons, Type)>) -> Vec<MorphScheme> {
    cons.iter()
    .map(|(n, c, t)| MorphScheme::from_type(n, c.clone(), t).expect(&format!("Cannot make MorphScheme from {}", t)))
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_sy::{Kind, t_var_0, t_gen, t_nat, t_int, t_double};
    use crate::cons::Cons::{Id, Data, Comp};
    use crate::cons::{pair};

    #[test]
    fn test_morph_scheme_new() {
       let m = MorphScheme::new(
           "f",
           Id,
           t_var_0("a"),
           t_var_0("a")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           cons: Id,
           scheme: Scheme{
               kinds : vec![Kind::Star],
               t : t_fun(t_gen(0), t_gen(0)),
           },
       };
       assert_eq!(m, expect);

       let m = MorphScheme::new(
           "f",
           Data(0),
           t_fun(t_var_0("a"), t_var_0("b")),
           t_var_0("b")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           cons: Data(0),
           scheme: Scheme{
               kinds : vec![Kind::Star, Kind::Star],
               t : t_fun(t_fun(t_gen(0), t_gen(1)), t_gen(1)),
           },
       };
       assert_eq!(m, expect);
    }

    // #[test]
    // fn test_morph_scheme_and_then() {
    //     let x = MorphScheme::new("x", Data(0), t_var_0("a"), t_var_0("b"));
    //     let y = MorphScheme::new("y", Data(1), t_var_0("b"), t_var_0("c"));
    //     let result = x.and_then(&y).unwrap();
    //     let expect = MorphScheme::new("y.x",
    //         pair(pair(Comp, Data(1)), Data(0)),
    //         t_var_0("a"),
    //         t_var_0("c"));
    //     assert_eq!(result, expect);

    //     let expect = Ok(MorphScheme::new("x.y",
    //         pair(Data(1), Data(0)),
    //         t_var_0("b"), t_var_0("d")));
    //     assert_eq!(y.and_then(&x), expect);

    //     let x = MorphScheme::new("x", Data(0), t_nat(), t_int());
    //     let y = MorphScheme::new("y", Data(1), t_int(), t_double());
    //     let result = x.and_then(&y);
    //     let expect = Ok(MorphScheme::new("y.x",
    //         pair(Data(0), Data(1)),
    //         t_nat(), t_double()));
    //     assert_eq!(result, expect);

    //     let result = y.and_then(&x);
    //     assert!(result.is_err(), "{:?}", result);
    // }

    #[test]
    fn test_morphism_from_scheme() {

       // f: a -> a; x: b
       let m = MorphScheme::new(
           "f",
           Data(0),
           t_var_0("a"),
           t_var_0("a")
       );
       let source = t_var_0("b");
       let result = m.inst_ap(&source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           cons: Data(0),
           source: t_var_0("b"),
           target: t_var_0("b")}
       );
       assert_eq!(result, expect);

       // f: a -> b; x: b
       let m = MorphScheme::new(
           "f",
           Data(0),
           t_var_0("a"),
           t_var_0("b")
       );
       let source = t_var_0("b");
       let result = m.inst_ap(&source);

       // b -> a
       let expect = Ok(Morphism{
           name: String::from("f"),
           cons: Data(0),
           source: t_var_0("b"),
           target: t_var_0("c")}
       );
       assert_eq!(result, expect);

       // f: (a -> b) -> ( (c -> a) -> (c -> b)); x: x -> y
       let m = MorphScheme::new(
           "f",
           Data(0),
           t_fun(t_var_0("a"), t_var_0("b")),
           t_fun(
               t_fun(t_var_0("c"), t_var_0("a")),
               t_fun(t_var_0("c"), t_var_0("b")))
       );
       let source = t_fun(t_var_0("x"), t_var_0("y"));
       let result = m.inst_ap(&source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           cons: Data(0),
           source: t_fun(t_var_0("x"), t_var_0("y")),
           target: t_fun(
               t_fun(t_var_0("c"), t_var_0("x")),
               t_fun(t_var_0("c"), t_var_0("y")))
       });
       assert_eq!(result, expect);
    }

    #[test]
    fn test_morphism_and_then() {
        let x = Morphism::new("x", Data(0), t_var_0("a"), t_var_0("b"));
        let y = Morphism::new("y", Data(1), t_var_0("b"), t_var_0("c"));
        let result = x.and_then(&y);
        let expect = Ok(Morphism::new("y.x",
            pair(pair(Comp, Data(1)), Data(0)),
            t_var_0("a"), t_var_0("d")));
        assert_eq!(result, expect);

        let expect = Ok(Morphism::new("x.y",
            pair(pair(Comp, Data(0)), Data(1)),
            t_var_0("b"), t_var_0("d")));
        assert_eq!(y.and_then(&x), expect);

        let x = Morphism::new("x", Data(0), t_nat(), t_int());
        let y = Morphism::new("y", Data(1), t_int(), t_double());
        let result = x.and_then(&y);
        let expect = Ok(Morphism::new("y.x",
            pair(pair(Comp, Data(1)), Data(0)),
            t_nat(), t_double()));
        assert_eq!(result, expect);

        let result = y.and_then(&x);
        assert!(result.is_err(), "{:?}", result);
    }

    // use crate::util::vec_to_string;

    // #[test]
    // fn test_edges() {
    //     let terms: Vec<(String, Type)> = vec!
    //       // 1: Nat
    //       [ (String::from("1"), t_nat())
    //       // 1: Int
    //       , (String::from("1"), t_int())
    //       // f: Nat -> Int
    //       , (String::from("f"), t_fun(t_nat(),t_int()))
    //       // g: a -> b
    //       , (String::from("g"), t_fun(t_var_0("a"), t_var_0("b")))
    //       // h: a -> b -> c
    //       //, Cons::new("h", t_fun(t_var_0("a"), t_fun(t_var_0("b"), t_var_0("c"))))
    //       ];

    //     let morph_schemes = morph_schemes_from_cons(&cat_cons(terms));


    //     // MorphismsBF from Nat
    //     let n = t_nat();
    //     let res = morphisms_from_source(&n, &morph_schemes);
    //     let expect = vec![
    //         // Applying function terms to n
    //         Morphism::new("f", Data(0), t_nat(), t_int()),
    //         Morphism::new("g", Data(1), t_nat(), t_var_0("b")),
    //         //Morphism::new("h", t_nat(), t_fun(t_var_0("b"), t_var_0("c"))),
    //         // Applying n to terms (None)
    //     ];
    //     assert_eq!(res, expect,
    //         "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
    //         n,
    //         vec_to_string(&morph_schemes, "\n"),
    //         vec_to_string(&res, "\n" ),
    //         vec_to_string(&expect, "\n" )
    //     );

    //     // MorphismsBF from Identity morphism a -> a.
    //     let n = t_fun(t_var_0("a"), t_var_0("a"));
    //     let res = morphisms_from_source(&n, &morph_schemes);
    //     let expect =
    //         vec![
    //              // Applying n to terms
    //              Morphism::new("&1", Data(0), t_fun(t_nat(), t_nat()), t_nat()),
    //              Morphism::new("&1", Data(0), t_fun(t_int(), t_int()), t_int()),
    //              Morphism::new("&f", Data(0),
    //                  t_fun(
    //                      t_fun(t_nat(), t_int()),
    //                      t_fun(t_nat(), t_int())),
    //                  t_fun(t_nat(), t_int())),
    //              Morphism::new("&f.<", Data(0),
    //                  t_fun(t_int(), t_int()),
    //                  t_fun(t_nat(), t_int())),
    //              Morphism::new("&g", Data(0),
    //                  t_fun(
    //                      t_fun(t_var_0("b"), t_var_0("c")),
    //                      t_fun(t_var_0("b"), t_var_0("c"))),
    //                  t_fun(t_var_0("b"), t_var_0("c"))),
    //              Morphism::new("&g.<", Data(0),
    //                  t_fun(t_var_0("a"), t_var_0("a")),
    //                  t_fun(t_var_0("d"), t_var_0("a"))),
    //              // Applying function terms to n
    //              Morphism::new("g", Data(0), t_fun(t_var_0("a"), t_var_0("a")), t_var_0("c")),
    //          ];
    //     assert_eq!(res, expect,
    //         "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
    //         n,
    //         vec_to_string(&morph_schemes, "\n"),
    //         vec_to_string(&res, "\n" ),
    //         vec_to_string(&expect, "\n" )
    //     );

    //     // MorphismsBF from a -> b
    //     let n = t_fun(t_var_0("a"), t_var_0("b"));
    //     let res = morphisms_from_source(&n, &morph_schemes);
    //     let expect =
    //         vec![
    //              Morphism::new("&1", Data(0), t_fun(t_nat(), t_var_0("b")), t_var_0("b")),
    //              Morphism::new("&1", Data(0), t_fun(t_int(), t_var_0("b")), t_var_0("b")),
    //              Morphism::new("&f", Data(0),
    //                  t_fun(
    //                      t_fun(t_nat(), t_int()),
    //                      t_var_0("b")),
    //                  t_var_0("b")),
    //              Morphism::new("&f.<", Data(0),
    //                  t_fun(t_int(), t_var_0("b")),
    //                  t_fun(t_nat(), t_var_0("b"))),
    //              Morphism::new("&g", Data(0),
    //                  t_fun(
    //                      t_fun(t_var_0("c"), t_var_0("d")),
    //                      t_var_0("b")),
    //                  t_var_0("b")),
    //              Morphism::new("&g.<", Data(0),
    //                  t_fun(t_var_0("a"), t_var_0("b")),
    //                  t_fun(t_var_0("e"), t_var_0("b"))),
    //              Morphism::new("g", Data(0), t_fun(t_var_0("a"), t_var_0("b")), t_var_0("d")),
    //          ];
    //     assert_eq!(res, expect,
    //         "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
    //         n,
    //         vec_to_string(&morph_schemes, "\n"),
    //         vec_to_string(&res, "\n" ),
    //         vec_to_string(&expect, "\n" )
    //     );

    //     // MorphismsBF from Int-> Int
    //     let n = t_fun(t_int(), t_int());
    //     let res = morphisms_from_source(&n, &morph_schemes);
    //     let expect =
    //         vec![
    //              Morphism::new("&1", Data(0), t_fun(t_int(), t_int()), t_int()),
    //              Morphism::new("&f.<", Data(0),
    //                  t_fun(t_int(), t_int()),
    //                  t_fun(t_nat(), t_int())),
    //              Morphism::new("&g.<", Data(0),
    //                  t_fun(t_int(), t_int()),
    //                  t_fun(t_var_0("c"), t_int())),
    //              Morphism::new("g", Data(0), t_fun(t_int(), t_int()), t_var_0("b")),
    //          ];
    //     assert_eq!(res, expect,
    //         "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
    //         n,
    //         vec_to_string(&morph_schemes, "\n"),
    //         vec_to_string(&res, "\n" ),
    //         vec_to_string(&expect, "\n" )
    //     );
    // }
}

