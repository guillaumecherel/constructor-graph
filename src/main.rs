mod util;
mod type_sy;

use std::collections::VecDeque;
use std::collections::HashSet;
use std::iter;
use std::iter::Iterator;
use std::fmt;

use type_sy::{mgu, VarNames, Type, var_names, fresh_inst, Tyvar, Subst, Scheme, Types, quantify};
use type_sy::{t_var_0, t_fun, t_fun_seq, t_int, t_nat, t_con, t_list_t, t_pair, t_double};

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
        let f = t_fun(source, target);
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
      let new_var = t_var_0(&candidates.next().expect("No available var name."));
      let label = ["&", &label].concat();
      MorphScheme::new(&label, t_fun(typ.clone(), new_var.clone()), new_var)
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
            t_fun(t_var_0("a"), t_var_0("b")),
            t_fun(
                t_fun(t_var_0("b"), t_var_0("c")),
                t_fun(t_var_0("a"), t_var_0("c"))
            )
        )
    }

    fn chain_backward() -> MorphScheme {
        MorphScheme::new("<",
            t_fun(t_var_0("b"), t_var_0("c")),
            t_fun(
                t_fun(t_var_0("a"), t_var_0("b")),
                t_fun(t_var_0("a"), t_var_0("c"))
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
           t_var_0("a"),
           t_var_0("a")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           scheme: Scheme{
               kinds : vec![Kind::Star],
               t : t_fun(tGen(0), tGen(0)),
           },
       };
       assert_eq!(m, expect);

       let m = MorphScheme::new(
           "f",
           t_fun(t_var_0("a"), t_var_0("b")),
           t_var_0("b")
       );
       let expect = MorphScheme{
           name: String::from("f"),
           scheme: Scheme{
               kinds : vec![Kind::Star, Kind::Star],
               t : t_fun(t_fun(tGen(0), tGen(1)), tGen(1)),
           },
       };
       assert_eq!(m, expect);
    }
}

#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Clone)]
#[derive(Debug)]
#[derive(Hash)]
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
        let i = fresh_inst(&ms.scheme, &mut candidates);
        let i_source = i.source().unwrap();
        mgu(&i_source, source).map(|u| {
            Morphism::new(
                &ms.name,
                i_source.apply_substitution(&u),
                i.target().unwrap().apply_substitution(&u),
            )
        })
    }

    fn format_dot_edge(&self) -> String {
        // "((-> Domain) Domain)" -> "Domain" [ label = "&unit_domain" ]
        "\"".to_owned() + &self.source.to_string() + "\""
        + " -> "
        + "\"" + &self.target.to_string() + "\""
        + " [ label = \"" + &self.name + "\" ]"
    }
}



impl fmt::Display for Morphism {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
     write!(f, "Morphism \"{}\": {} --> {}", self.name, self.source, self.target)
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
           t_var_0("a"),
           t_var_0("a")
       );
       let source = t_var_0("b");
       let result = Morphism::from_scheme(&m, &source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: t_var_0("b"),
           target: t_var_0("b")}
       );
       assert_eq!(result, expect);

       // f: a -> b; x: b
       let m = MorphScheme::new(
           "f",
           t_var_0("a"),
           t_var_0("b")
       );
       let source = t_var_0("b");
       let result = Morphism::from_scheme(&m, &source);

       // b -> a
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: t_var_0("b"),
           target: t_var_0("c")}
       );
       assert_eq!(result, expect);

       // f: (a -> b) -> ( (c -> a) -> (c -> b)); x: x -> y
       let m = MorphScheme::new(
           "f",
           t_fun(t_var_0("a"), t_var_0("b")),
           t_fun(
               t_fun(t_var_0("c"), t_var_0("a")),
               t_fun(t_var_0("c"), t_var_0("b")))
       );
       let source = t_fun(t_var_0("x"), t_var_0("y"));
       let result = Morphism::from_scheme(&m, &source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: t_fun(t_var_0("x"), t_var_0("y")),
           target: t_fun(
               t_fun(t_var_0("c"), t_var_0("x")),
               t_fun(t_var_0("c"), t_var_0("y")))
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
 
 
fn edges_from(source: &Type, mss: &Vec<MorphScheme>) -> Vec<Morphism> {
   mss.iter().filter_map(|ms: &MorphScheme| -> Option<Morphism> {
       Morphism::from_scheme(ms, source).ok()
   }).collect()
}

struct Edges {
    queue: VecDeque<Morphism>,
    morph_schemes: Vec<MorphScheme>,
}

impl Iterator for Edges {
    type Item = Morphism;

    fn next(&mut self) -> Option<Self::Item> {
        match self.queue.pop_front() {
            None => None,
            Some(m) => {
                let next = edges_from(&m.target, &self.morph_schemes);
                self.queue.extend(next.into_iter());
                Some (m)
            }
        }
    }
}

fn edges_from_terms(terms: &Vec<Term>, mss: &Vec<MorphScheme>) -> Edges {
    Edges {
        queue: terms.iter().flat_map(|Term(_, t)| edges_from(t, mss)).collect(),
        morph_schemes: mss.clone(),
    }
}

#[cfg(test)]
mod tests_edges {
    use super::*;
    use util::vec_to_string;

    #[test]
    fn test_edges() {
        let terms: Vec<Term> = vec!
          [ Term::new("1", t_nat())
          , Term::new("1", t_int())
          , Term::new("f", t_fun(t_nat(),t_int()))
          , Term::new("g", t_fun(t_var_0("a"), t_var_0("b")))
          ];

        let morph_schemes = morph_schemes_from_terms(&terms);

        // Edges from Nat
        let n = t_nat();
        assert_eq!(
            edges_from(&n, &morph_schemes),
            vec![Morphism::new("f", t_nat(), t_int()),
                 Morphism::new("g", t_nat(), t_var_0("b"))]
        );

        // Edges from Identity morphism a -> a.
        let n = t_fun(t_var_0("a"), t_var_0("a"));
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", tFun(t_nat(), t_nat()), t_nat()),
                 Morphism::new(".1", tFun(t_int(), t_int()), t_int()),
                 Morphism::new(".f",
                     tFun(
                         tFun(t_nat(), t_int()),
                         tFun(t_nat(), t_int())),
                     tFun(t_nat(), t_int())),
                 Morphism::new(".g",
                     tFun(
                         tFun(t_var_0("b"), t_var_0("c")),
                         tFun(t_var_0("b"), t_var_0("c"))),
                     tFun(t_var_0("b"), t_var_0("c"))),
                 Morphism::new("g", tFun(t_var_0("a"), t_var_0("a")), t_var_0("c")),
                 Morphism::new(">",
                     tFun(t_var_0("a"), t_var_0("a")),
                     tFun(
                         tFun(t_var_0("a"), t_var_0("d")),
                         tFun(t_var_0("a"), t_var_0("d"))
                     )
                 ),
                 Morphism::new("<",
                     tFun(t_var_0("a"), t_var_0("a")),
                     tFun(
                         tFun(t_var_0("d"), t_var_0("a")),
                         tFun(t_var_0("d"), t_var_0("a"))
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
        let n = tFun(t_var_0("a"), t_var_0("b"));
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", tFun(t_nat(), t_var_0("b")), t_var_0("b")),
                 Morphism::new(".1", tFun(t_int(), t_var_0("b")), t_var_0("b")),
                 Morphism::new(".f",
                     tFun(
                         tFun(t_nat(), t_int()),
                         t_var_0("b")),
                     t_var_0("b")),
                 Morphism::new(".g",
                     tFun(
                         tFun(t_var_0("c"), t_var_0("d")),
                         t_var_0("b")),
                     t_var_0("b")),
                 Morphism::new("g", tFun(t_var_0("a"), t_var_0("b")), t_var_0("d")),
                 Morphism::new(">",
                     tFun(t_var_0("a"), t_var_0("b")),
                     tFun(
                         tFun(t_var_0("b"), t_var_0("e")),
                         tFun(t_var_0("a"), t_var_0("e"))
                     )
                 ),
                 Morphism::new("<",
                     tFun(t_var_0("a"), t_var_0("b")),
                     tFun(
                         tFun(t_var_0("e"), t_var_0("a")),
                         tFun(t_var_0("e"), t_var_0("b"))
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
        let n = tFun(t_int(), t_int());
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new(".1", t_fun(t_int(), t_int()), t_int()),
                 Morphism::new("g", t_fun(t_int(), t_int()), t_var_0("b")),
                 Morphism::new(">",
                     t_fun(t_int(), t_int()),
                     t_fun(
                         t_fun(t_int(), t_var_0("c")),
                         t_fun(t_int(), t_var_0("c"))
                     )
                 ),
                 Morphism::new("<",
                     t_fun(t_int(), t_int()),
                     t_fun(
                         t_fun(t_var_0("c"), t_int()),
                         t_fun(t_var_0("c"), t_int())
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
    let id : Term = Term::new("identity", t_fun(t_var_0("a"), t_var_0("a")));
    
    let initial: Vec<Term> = vec![
        Term::new("netlogo_source", t_con("File")),
        Term::new("netlogo_setup", t_con("Setup")),
        Term::new("seed", t_con("Seed")),
        Term::new("unit_domain", t_con("Domain")),
        Term::new("uniform_prior", t_con("Prior")),
        Term::new("lhsSampleSize", t_con("LhsSampleSize")),
    ];
    
    let functions: Vec<Term> = vec![
        Term::new("bounded_domain",
            t_fun_seq(&[t_list_t(t_pair(t_double(), t_double())), t_con("Domain")])),
        Term::new("netlogo",
            t_fun_seq(&[t_con("File"), t_con("Setup"), t_con("Seed"), t_con("Model")])),
        Term::new("lhs",
            t_fun_seq(&[t_con("Domain"), t_con("LhsSampleSize"), t_con("Seed"), t_con("Sampling")])),
        Term::new("direct_sampling",
            t_fun_seq(&[t_con("Model"), t_con("Sample"), t_con("Sample")])),
        Term::new("median",
            t_fun_seq(&[t_con("Sample"), t_con("Median")])),
        Term::new("abc",
            t_fun_seq(&[t_con("Model"), t_con("Prior"), t_con("Posterior")])),
    ];

    let terminal: Vec<Term> = vec![
        Term::new("done", t_fun_seq(&[t_con("Posterior"), t_con("DONE")])),
        Term::new("done", t_fun_seq(&[t_con("Median"), t_con("DONE")])),
    ];

    let terms: Vec<Term> =
        initial.iter()
        .chain(functions.iter())
        .chain(terminal.iter())
        .cloned().collect();

    println!("Terms:");
    for t in terms.iter() {
      println!("    {}", t);
    }

    let morph_schemes = morph_schemes_from_terms(&terms);

    println!("Morph Schemes:");
    for m in morph_schemes.iter() {
      println!("    {}", m);
    }

    // println!("Edges from identity:");
    // for m in edges_from_terms(&vec![id], &morph_schemes) {
    //     println!("{}", m.format_dot_edge());
    // }

    let edges_set: HashSet<Morphism> = edges_from_terms(&vec![id], &morph_schemes).take(1000).collect();
    println!("digraph {{");
    for m in edges_set {
        println!("{}", m.format_dot_edge());
    }
    println!("}}");
}

