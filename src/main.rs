mod util;
mod type_sy;

use std::collections::VecDeque;
use std::iter;
use std::iter::Iterator;
use std::fmt;

use util::vec_to_string;
use type_sy::{Kind, HasKind, tGen, Scheme, Type, Tyvar, Types, Subst, tVar0, tFun, mgu, VarNames, var_names, quantify, freshInst,
              tNat, tInt};

#[derive(Debug)]
#[derive(Clone)]
struct Term(String, Type);

impl Term {
    fn new(name: &str, t: Type) -> Term {
       Term(String::from(name), t)
    }
}

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Term(name, typ) => write!(f, "{}: {}", name, typ),
    }
  }
}

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Clone)]
#[derive(Debug)]
struct MorphScheme {
  name: String,
  scheme: Scheme,
}

impl MorphScheme {
    fn new(name: &str, source: Type, target: Type) -> MorphScheme {
        let f = tFun(source, target);
        MorphScheme {
            name : String::from(name),
            scheme : quantify(None,&f),
        }
    }

    // Return None if t is not a function type (TAp)
    fn from_type(name: &str, t: &Type) -> Option<MorphScheme> {
        match t {
             Type::TAp(_, _) => {
                 let s : Scheme = quantify(None, &t);
                 Some(MorphScheme {
                         name: String::from(name),
                         scheme: s,
                 })
             },
             _ => None,
       }
    }

    // Create a morphism f: a -> b from a function term a -> b. Return None if the given
    // term is not a function.
    fn from_function(Term(label, typ): &Term) -> Option<MorphScheme> {
        MorphScheme::from_type(label, typ)
    }

    // Create a morphism scheme (.x): ((a -> b) -> b) from the given term x: a such that (.x) g = g x.
    fn ap(Term(label, typ): &Term) -> MorphScheme {
      let used_var_names = var_names(typ).into_iter().cloned();
      let mut candidates = VarNames::new().exclude_all(used_var_names);
      let new_var = tVar0(&candidates.next().expect("No available var name."));
      let label = [".", &label].concat();
      MorphScheme::new(&label, tFun(typ.clone(), new_var.clone()), new_var)
    }


    // // Transform self into the type that results from the application of t to self.
    // // Get the mgu between self.source and t and return the result of applying the
    // // substitutions to the whole morphism.
    // fn subst_ap(&self, t: &Type) -> Option<MorphScheme> {
    //     mgu(&self.source, t).map(|subst| {
    //         MorphScheme {
    //             name: self.name.clone(),
    //             source: self.source.apply_substitution(&subst),
    //             target: self.target.apply_subst_disambig(subst.clone()).1
    //         }
    //     })
    // }

    fn chain_forward() -> MorphScheme {
        MorphScheme::new(">",
            tFun(tVar0("a"), tVar0("b")),
            tFun(
                tFun(tVar0("b"), tVar0("c")),
                tFun(tVar0("a"), tVar0("c"))
            )
        )
    }

    fn chain_backward() -> MorphScheme {
        MorphScheme::new("<",
            tFun(tVar0("b"), tVar0("c")),
            tFun(
                tFun(tVar0("a"), tVar0("b")),
                tFun(tVar0("a"), tVar0("c"))
            )
        )
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
}



impl Types for MorphScheme {
    fn apply_substitution(&self, substitution: &Subst) -> MorphScheme {
       MorphScheme {
           name: self.name.clone(),
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
      MorphScheme{name, scheme} => write!(f, "{}: {} ", name, scheme),
    }
  }
}

#[cfg(test)]
mod tests_morph_scheme {
    use super::*;

    #[test]
    fn test_morph_scheme_new() {
       let m = MorphScheme::new(
           "f",
           tVar0("a"),
           tVar0("a")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           scheme: Scheme{
               kinds : vec![Kind::Star],
               t : tFun(tGen(0), tGen(0)),
           },
       };
       assert_eq!(m, expect);

       let m = MorphScheme::new(
           "f",
           tFun(tVar0("a"), tVar0("b")),
           tVar0("b")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           scheme: Scheme{
               kinds : vec![Kind::Star, Kind::Star],
               t : tFun(tFun(tGen(0), tGen(1)), tGen(1)),
           },
       };
       assert_eq!(m, expect);
    }
}

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Clone)]
#[derive(Debug)]
struct Morphism {
  name: String,
  source: Type,
  target: Type,
}

impl Morphism {
    fn new(name: &str, source: Type, target: Type) -> Morphism {
        Morphism {
            name : String::from(name),
            source : source,
            target : target,
        }
    }

    // Return the morphism m where the m.source and m.target are built by
    // applying the substitution (mgu ms.source source) to ms.source and ms.target.
    // Return None if the mgu does not exist.
    fn from_scheme(ms: &MorphScheme, source: &Type) -> Result<Morphism, String> {
        let used_var_names = var_names(source).into_iter().cloned();
        let mut candidates = VarNames::new().exclude_all(used_var_names);
        let i = freshInst(&ms.scheme, &mut candidates);
        let i_source = i.source().unwrap();
        mgu(&i_source, source).map(|u| {
            Morphism::new(
                &ms.name,
                i_source.apply_substitution(&u),
                i.target().unwrap().apply_substitution(&u),
            )
        })
    }
}



impl fmt::Display for Morphism {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
     write!(f, "Morphism {}, {} --> {}", self.name, self.source, self.target)
  }
}

#[cfg(test)]
mod tests_morphism {
    use super::*;

    #[test]
    fn test_morphism_from_scheme() {

       // f: a -> a; x: b
       let m = MorphScheme::new(
           "f",
           tVar0("a"),
           tVar0("a")
       );
       let source = tVar0("b");
       let result = Morphism::from_scheme(&m, &source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: tVar0("b"),
           target: tVar0("b")}
       );
       assert_eq!(result, expect);

       // f: a -> b; x: b
       let m = MorphScheme::new(
           "f",
           tVar0("a"),
           tVar0("b")
       );
       let source = tVar0("b");
       let result = Morphism::from_scheme(&m, &source);

       // b -> a
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: tVar0("b"),
           target: tVar0("c")}
       );
       assert_eq!(result, expect);

       // f: (a -> b) -> ( (c -> a) -> (c -> b)); x: x -> y
       let m = MorphScheme::new(
           "f",
           tFun(tVar0("a"), tVar0("b")),
           tFun(
               tFun(tVar0("c"), tVar0("a")),
               tFun(tVar0("c"), tVar0("b")))
       );
       let source = tFun(tVar0("x"), tVar0("y"));
       let result = Morphism::from_scheme(&m, &source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: tFun(tVar0("x"), tVar0("y")),
           target: tFun(
               tFun(tVar0("c"), tVar0("x")),
               tFun(tVar0("c"), tVar0("y")))
       });
       assert_eq!(result, expect);
    }
}


fn morph_schemes_from_terms(terms: &Vec<Term>) -> Vec<MorphScheme> {
      terms.iter().map(|t| MorphScheme::ap(t))
      .chain(terms.iter().filter_map(|t| MorphScheme::from_function(t)))
      .chain(iter::once(MorphScheme::chain_forward()))
      .chain(iter::once(MorphScheme::chain_backward()))
      .collect()
}
 
 
fn edges(source: &Type, mss: &Vec<MorphScheme>) -> Vec<Morphism> {
   mss.iter().filter_map(|ms: &MorphScheme| -> Option<Morphism> {
       Morphism::from_scheme(ms, source).ok()
   }).collect()
}

// fn paths()

#[cfg(test)]
mod tests_edges {
    use super::*;

    #[test]
    fn test_edges() {
        let terms: Vec<Term> = vec!
          [ Term::new("1", tNat())
          , Term::new("1", tInt())
          , Term::new("f", tFun(tNat(),tInt()))
          , Term::new("g", tFun(tVar0("a"), tVar0("b")))
          ];

        let morph_schemes = morph_schemes_from_terms(&terms);

        // Edges from Nat
        let n = tNat();
        assert_eq!(
            edges(&n, &morph_schemes),
            vec![Morphism::new("f", tNat(), tInt()),
                 Morphism::new("g", tNat(), tVar0("b"))]
        );

        // Edges from Identity morphism a -> a.
        let n = tFun(tVar0("a"), tVar0("a"));
        let res = edges(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", tFun(tNat(), tNat()), tNat()),
                 Morphism::new(".1", tFun(tInt(), tInt()), tInt()),
                 Morphism::new(".f",
                     tFun(
                         tFun(tNat(), tInt()),
                         tFun(tNat(), tInt())),
                     tFun(tNat(), tInt())),
                 Morphism::new(".g",
                     tFun(
                         tFun(tVar0("b"), tVar0("c")),
                         tFun(tVar0("b"), tVar0("c"))),
                     tFun(tVar0("b"), tVar0("c"))),
                 Morphism::new("g", tFun(tVar0("a"), tVar0("a")), tVar0("c")),
                 Morphism::new(">",
                     tFun(tVar0("a"), tVar0("a")),
                     tFun(
                         tFun(tVar0("a"), tVar0("d")),
                         tFun(tVar0("a"), tVar0("d"))
                     )
                 ),
                 Morphism::new("<",
                     tFun(tVar0("a"), tVar0("a")),
                     tFun(
                         tFun(tVar0("d"), tVar0("a")),
                         tFun(tVar0("d"), tVar0("a"))
                     )
                 ),
             ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );

        // Edges from a -> b
        let n = tFun(tVar0("a"), tVar0("b"));
        let res = edges(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", tFun(tNat(), tVar0("b")), tVar0("b")),
                 Morphism::new(".1", tFun(tInt(), tVar0("b")), tVar0("b")),
                 Morphism::new(".f",
                     tFun(
                         tFun(tNat(), tInt()),
                         tVar0("b")),
                     tVar0("b")),
                 Morphism::new(".g",
                     tFun(
                         tFun(tVar0("c"), tVar0("d")),
                         tVar0("b")),
                     tVar0("b")),
                 Morphism::new("g", tFun(tVar0("a"), tVar0("b")), tVar0("d")),
                 Morphism::new(">",
                     tFun(tVar0("a"), tVar0("b")),
                     tFun(
                         tFun(tVar0("b"), tVar0("e")),
                         tFun(tVar0("a"), tVar0("e"))
                     )
                 ),
                 Morphism::new("<",
                     tFun(tVar0("a"), tVar0("b")),
                     tFun(
                         tFun(tVar0("e"), tVar0("a")),
                         tFun(tVar0("e"), tVar0("b"))
                     )
                 ),
             ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );

        // Edges from Int-> Int
        let n = tFun(tInt(), tInt());
        let res = edges(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", tFun(tInt(), tInt()), tInt()),
                 Morphism::new("g", tFun(tInt(), tInt()), tVar0("b")),
                 Morphism::new(">",
                     tFun(tInt(), tInt()),
                     tFun(
                         tFun(tInt(), tVar0("c")),
                         tFun(tInt(), tVar0("c"))
                     )
                 ),
                 Morphism::new("<",
                     tFun(tInt(), tInt()),
                     tFun(
                         tFun(tVar0("c"), tInt()),
                         tFun(tVar0("c"), tInt())
                     )
                 ),
             ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );
    }
}


fn main() {
// 
//   let terms: Vec<Term> = vec!
//       [ Term::new("1", Type::Nat)
//       , Term::new("1", Type::Int)
//       , Term::new("f", Type::fun(Type::Nat,Type::Int))
//       , Term::new("g", Type::fun(Type::var("a"), Type::var("b")))
//       ];
// 
//   for t in terms.iter() {
//     println!("Term: {}", t);
//  }
//
//  let morphisms = morphisms_from_terms(&terms);
//
//  for m in morphisms.iter() {
//    println!("Morphism: {}", m);
//  }
//
}
