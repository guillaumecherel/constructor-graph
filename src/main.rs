mod util;
mod type_sy;

use std::collections::VecDeque;
use std::collections::HashSet;
use std::iter;
use std::iter::Iterator;
use std::fmt;
use structopt::StructOpt;

use type_sy::{mgu, VarNames, Type, var_names, fresh_inst, Tyvar, Subst, Scheme, Types, quantify, arity, Kind};
use type_sy::{t_var_0, t_fun, t_fun_seq, t_int, t_nat, t_con, t_list_t, t_pair, t_double, t_gen};

#[derive(Debug)]
#[derive(Clone)]
struct Term(String, Type);

impl Term {
    fn new(name: &str, t: Type) -> Term {
       Term(String::from(name), t)
    }

    fn arity(&self) -> u32 {
       match self {Term(_, t) => arity(t)}
    }

    fn source(&self) -> Result<&Type, String> {
       let Term(_, t) = self;
       t.source()
    }

    fn target(&self) -> Result<&Type, String> {
       let Term(_, t) = self;
       t.target()
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
    fn from_term(Term(label, typ): &Term) -> Option<MorphScheme> {
        MorphScheme::from_type(label, typ)
    }

    // Create a morphism scheme (.x): ((a -> b) -> b) from the given term x: a such that (.x) g = g x.
    fn ap(Term(label, typ): &Term) -> MorphScheme {
      let mut candidates = VarNames::excluding(var_names(typ).into_iter());
      let new_var = t_var_0(&candidates.next().expect("No available var name."));
      let label = ["&", &label].concat();
      MorphScheme::new(&label, t_fun(typ.clone(), new_var.clone()), new_var)
    }

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

    // Forward composition: given self: X -> Y and m: Y -> Z, self.compose(m) : X -> Z.
    fn and_then(&self, m: &MorphScheme) -> Result<MorphScheme, String> {
        let mut vn = VarNames::excluding(
            var_names(&self.scheme).into_iter()
            .chain(var_names(&m.scheme).into_iter())
         );
        let si = fresh_inst(&self.scheme, &mut vn);
        let mi = fresh_inst(&m.scheme, &mut vn);
        mgu(&si.target().unwrap(), &mi.source().unwrap()).map(|u| {
            MorphScheme::new(
                &(m.name.to_owned()  + "." + &self.name),
                si.source().unwrap().apply_substitution(&u),
                mi.target().unwrap().apply_substitution(&u),
            )
        })
    }

    // Return the morphism that resuls from applying arg to the function represented
    // by self. Creates a fresh instance i of self avoiding any type variable name clash
    // with the argument by excluding from the new variable name any name that appears in arg,
    // then computes s = (mgu i.source() arg) and applies it to both i.source() and i.target().
    // Return None if the mgu does not exist.
    fn inst_ap(&self, arg: &Type) -> Result<Morphism, String> {
        let mut vn = VarNames::excluding(var_names(arg).into_iter());
        let i = fresh_inst(&self.scheme, &mut vn);
        let i_source = i.source()?;
        mgu(&i_source, arg).map(|u| {
            Morphism::new(
                &self.name,
                i_source.apply_substitution(&u),
                i.target().unwrap().apply_substitution(&u),
            )
        })
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
               t : t_fun(t_gen(0), t_gen(0)),
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
               t : t_fun(t_fun(t_gen(0), t_gen(1)), t_gen(1)),
           },
       };
       assert_eq!(m, expect);
    }

    #[test]
    fn test_and_then() {
        let x = MorphScheme::new("x", t_var_0("a"), t_var_0("b"));
        let y = MorphScheme::new("y", t_var_0("b"), t_var_0("c"));
        let result = x.and_then(&y);
        let expect = Ok(MorphScheme::new("y.x", t_var_0("a"), t_var_0("c")));
        assert_eq!(result, expect);

        let expect = Ok(MorphScheme::new("x.y", t_var_0("b"), t_var_0("d")));
        assert_eq!(y.and_then(&x), expect);

        let x = MorphScheme::new("x", t_nat(), t_int());
        let y = MorphScheme::new("y", t_int(), t_double());
        let result = x.and_then(&y);
        let expect = Ok(MorphScheme::new("y.x", t_nat(), t_double()));
        assert_eq!(result, expect);

        let result = y.and_then(&x);
        assert!(result.is_err(), "{:?}", result);
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

    // Forward composition: given self: X -> Y and m: Y -> Z, self.compose(m) : X -> Z.
    fn and_then(&self, m: &Morphism) -> Result<Morphism, String> {
        let mut vn = VarNames::excluding(
            var_names(&self.source).into_iter()
            .chain(var_names(&self.target).into_iter())
        );
        let q = quantify(None, &t_fun(m.source.clone(), m.target.clone()));
        let i = fresh_inst(&q, &mut vn);
        mgu(&self.target, &i.source().unwrap()).map(|u| {
            Morphism::new(
                &(m.name.to_owned() + "." + &self.name),
                self.source.apply_substitution(&u),
                i.target().unwrap().apply_substitution(&u),
            )
        })
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
       let result = m.inst_ap(&source);
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
       let result = m.inst_ap(&source);

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
       let result = m.inst_ap(&source);
       let expect = Ok(Morphism{
           name: String::from("f"),
           source: t_fun(t_var_0("x"), t_var_0("y")),
           target: t_fun(
               t_fun(t_var_0("c"), t_var_0("x")),
               t_fun(t_var_0("c"), t_var_0("y")))
       });
       assert_eq!(result, expect);
    }

    #[test]
    fn test_and_then() {
        let x = Morphism::new("x", t_var_0("a"), t_var_0("b"));
        let y = Morphism::new("y", t_var_0("b"), t_var_0("c"));
        let result = x.and_then(&y);
        let expect = Ok(Morphism::new("y.x", t_var_0("a"), t_var_0("d")));
        assert_eq!(result, expect);

        let expect = Ok(Morphism::new("x.y", t_var_0("b"), t_var_0("d")));
        assert_eq!(y.and_then(&x), expect);

        let x = Morphism::new("x", t_nat(), t_int());
        let y = Morphism::new("y", t_int(), t_double());
        let result = x.and_then(&y);
        let expect = Ok(Morphism::new("y.x", t_nat(), t_double()));
        assert_eq!(result, expect);

        let result = y.and_then(&x);
        assert!(result.is_err(), "{:?}", result);
    }
}


fn morph_schemes_from_terms(terms: &Vec<Term>) -> Vec<MorphScheme> {
      // attention à ne pas introduire de doublons avec les shortcuts.
      // terms.iter().map(|t| MorphScheme::ap(t))
      terms.iter().flat_map(shortcuts)
      .chain(terms.iter().filter_map(|t| MorphScheme::from_term(t)))
      //.chain(iter::once(MorphScheme::chain_forward()))
      //.chain(iter::once(MorphScheme::chain_backward()))
      .collect()
}

// Returns [&h, &h . <, &h . < . <, ... , &h . < ... . <], where the last element
// is composed of a number of successive < equal to h's arity.
fn shortcuts(term: &Term) -> Vec<MorphScheme> {
    iter::successors(
        Some((0, MorphScheme::ap(term))),
        |(length,t)|
            if *length >= term.arity() {
                None
            } else {
                MorphScheme::chain_backward().and_then(t)
                    .map(|m| (length + 1, m))
                    .ok()
            }
        )
    .map(|(_, t)| t)
    .collect()
}
 

fn edges_from(source: &Type, mss: &Vec<MorphScheme>) -> Vec<Morphism> {
    mss.iter().filter_map(|ms: &MorphScheme| -> Option<Morphism> {
        ms.inst_ap(source).ok()
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

fn edges_from_terms(terms: &Vec<&Term>, mss: &Vec<MorphScheme>) -> Edges {
    let q = terms.iter().flat_map(|Term(_, t)| edges_from(t, mss)).collect();
    Edges {
        queue: q,
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
          // 1: Nat
          [ Term::new("1", t_nat())
          // 1: Int
          , Term::new("1", t_int())
          // f: Nat -> Int
          , Term::new("f", t_fun(t_nat(),t_int()))
          // g: a -> b
          , Term::new("g", t_fun(t_var_0("a"), t_var_0("b")))
          // h: a -> b -> c
          //, Term::new("h", t_fun(t_var_0("a"), t_fun(t_var_0("b"), t_var_0("c"))))
          ];

        let morph_schemes = morph_schemes_from_terms(&terms);

        // Edges from Nat
        let n = t_nat();
        let res = edges_from(&n, &morph_schemes);
        let expect = vec![
            // Applying function terms to n
            Morphism::new("f", t_nat(), t_int()),
            Morphism::new("g", t_nat(), t_var_0("b")),
            //Morphism::new("h", t_nat(), t_fun(t_var_0("b"), t_var_0("c"))),
            // Applying n to terms (None)
        ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );

        // Edges from Identity morphism a -> a.
        let n = t_fun(t_var_0("a"), t_var_0("a"));
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 // Applying n to terms
                 Morphism::new("&1", t_fun(t_nat(), t_nat()), t_nat()),
                 Morphism::new("&1", t_fun(t_int(), t_int()), t_int()),
                 Morphism::new("&f",
                     t_fun(
                         t_fun(t_nat(), t_int()),
                         t_fun(t_nat(), t_int())),
                     t_fun(t_nat(), t_int())),
                 Morphism::new("&f.<",
                     t_fun(t_int(), t_int()),
                     t_fun(t_nat(), t_int())),
                 Morphism::new("&g",
                     t_fun(
                         t_fun(t_var_0("b"), t_var_0("c")),
                         t_fun(t_var_0("b"), t_var_0("c"))),
                     t_fun(t_var_0("b"), t_var_0("c"))),
                 Morphism::new("&g.<",
                     t_fun(t_var_0("a"), t_var_0("a")),
                     t_fun(t_var_0("d"), t_var_0("a"))),
                 // Applying function terms to n
                 Morphism::new("g", t_fun(t_var_0("a"), t_var_0("a")), t_var_0("c")),
                 //Morphism::new("h", t_fun(t_fun(t_var_0("a"), t_var_0("a")), t_var_0("a")), t_var_0("c")),
                 // Morphism::new(">",
                 //     t_fun(t_var_0("a"), t_var_0("a")),
                 //     t_fun(
                 //         t_fun(t_var_0("a"), t_var_0("d")),
                 //         t_fun(t_var_0("a"), t_var_0("d"))
                 //     )
                 // ),
                 // Morphism::new("<",
                 //     t_fun(t_var_0("a"), t_var_0("a")),
                 //     t_fun(
                 //         t_fun(t_var_0("d"), t_var_0("a")),
                 //         t_fun(t_var_0("d"), t_var_0("a"))
                 //     )
                 // ),
             ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );

        // Edges from a -> b
        let n = t_fun(t_var_0("a"), t_var_0("b"));
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new("&1", t_fun(t_nat(), t_var_0("b")), t_var_0("b")),
                 Morphism::new("&1", t_fun(t_int(), t_var_0("b")), t_var_0("b")),
                 Morphism::new("&f",
                     t_fun(
                         t_fun(t_nat(), t_int()),
                         t_var_0("b")),
                     t_var_0("b")),
                 Morphism::new("&f.<",
                     t_fun(t_int(), t_var_0("b")),
                     t_fun(t_nat(), t_var_0("b"))),
                 Morphism::new("&g",
                     t_fun(
                         t_fun(t_var_0("c"), t_var_0("d")),
                         t_var_0("b")),
                     t_var_0("b")),
                 Morphism::new("&g.<",
                     t_fun(t_var_0("a"), t_var_0("b")),
                     t_fun(t_var_0("e"), t_var_0("b"))),
                 Morphism::new("g", t_fun(t_var_0("a"), t_var_0("b")), t_var_0("d")),
                 // Morphism::new(">",
                 //     t_fun(t_var_0("a"), t_var_0("b")),
                 //     t_fun(
                 //         t_fun(t_var_0("b"), t_var_0("e")),
                 //         t_fun(t_var_0("a"), t_var_0("e"))
                 //     )
                 // ),
                 // Morphism::new("<",
                 //     t_fun(t_var_0("a"), t_var_0("b")),
                 //     t_fun(
                 //         t_fun(t_var_0("e"), t_var_0("a")),
                 //         t_fun(t_var_0("e"), t_var_0("b"))
                 //     )
                 // ),
             ];
        assert_eq!(res, expect,
            "\nnode: {} \nMorphSchemes: {} \nleft: {} \nright: {}",
            n,
            vec_to_string(&morph_schemes, "\n"),
            vec_to_string(&res, "\n" ),
            vec_to_string(&expect, "\n" )
        );

        // Edges from Int-> Int
        let n = t_fun(t_int(), t_int());
        let res = edges_from(&n, &morph_schemes);
        let expect =
            vec![
                 Morphism::new("&1", t_fun(t_int(), t_int()), t_int()),
                 Morphism::new("&f.<",
                     t_fun(t_int(), t_int()),
                     t_fun(t_nat(), t_int())),
                 Morphism::new("&g.<",
                     t_fun(t_int(), t_int()),
                     t_fun(t_var_0("c"), t_int())),
                 Morphism::new("g", t_fun(t_int(), t_int()), t_var_0("b")),
                 // Morphism::new(">",
                 //     t_fun(t_int(), t_int()),
                 //     t_fun(
                 //         t_fun(t_int(), t_var_0("c")),
                 //         t_fun(t_int(), t_var_0("c"))
                 //     )
                 // ),
                 // Morphism::new("<",
                 //     t_fun(t_int(), t_int()),
                 //     t_fun(
                 //         t_fun(t_var_0("c"), t_int()),
                 //         t_fun(t_var_0("c"), t_int())
                 //     )
                 // ),
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

#[derive(StructOpt)]
#[derive(Debug)]
struct Cli {
    #[structopt(subcommand)]
    output_type: Option<OutputType>,
}

#[derive(StructOpt)]
#[derive(Debug)]
enum OutputType {
    Info,
    GraphViz,
}

impl Default for OutputType {
    fn default() -> Self { OutputType::Info }
}



fn main() {
    let args = Cli::from_args();
    let (t, ms) = test_input();
    match args.output_type {
       None => output_info(&t, &ms),
       Some(OutputType::Info) => output_info(&t, &ms),
       Some(OutputType::GraphViz) => output_gv(&t, &ms),
       Some(x) => panic!("Unknown option: {:?}", x),
    }
}

fn test_input() -> (Vec<Term>, Vec<MorphScheme>) {
    let terms: Vec<Term> = vec![
        Term::new("netlogo_source", t_con("NetlogoSource")),
        Term::new("scala_source", t_con("ScalaSource")),
        Term::new("netlogo_setup", t_con("Setup")),
        Term::new("seed", t_con("Seed")),
        Term::new("unit_domain", t_con("Domain")),
        Term::new("uniform_prior", t_con("Prior")),
        Term::new("lhsSampleSize", t_con("LhsSampleSize")),
        Term::new("some_bounds", t_list_t(t_pair(t_double(), t_double()))),
        Term::new("bounded_domain",
            t_fun_seq(&[t_list_t(t_pair(t_double(), t_double())), t_con("Domain")])),
        Term::new("netlogo",
            t_fun_seq(&[t_con("NetlogoSource"), t_con("Setup"), t_con("Seed"), t_con("Model")])),
        Term::new("scala_model",
            t_fun_seq(&[t_con("ScalaSource"), t_con("Seed"), t_con("Model")])),
        Term::new("lhs",
            t_fun_seq(&[t_con("Domain"), t_con("LhsSampleSize"), t_con("Seed"), t_con("Sample")])),
        Term::new("direct_sampling",
            t_fun_seq(&[t_con("Model"), t_con("Sample"), t_con("Sample")])),
        Term::new("median",
            t_fun_seq(&[t_con("Sample"), t_con("Median")])),
        Term::new("abc",
            t_fun_seq(&[t_con("Model"), t_con("Prior"), t_con("Posterior")])),
        Term::new("calibrate",
            t_fun_seq(&[t_con("START"), t_con("Posterior"), t_con("OMS")])),
        Term::new("agg_stats",
            t_fun_seq(&[t_con("START"), t_con("Median"), t_con("OMS")])),
        Term::new("agg_stats",
            t_fun_seq(&[t_con("START"), t_con("Median"), t_con("OMS")])),
    ];

    let morph_schemes = morph_schemes_from_terms(&terms);

    (terms, morph_schemes)
}

fn start_nodes(terms: &Vec<Term>) -> Vec<&Term> {
    let start_node = t_con("START");
    terms.iter()
    .filter(|t|
        t.source()
        .map_or(false, |src| src == &start_node) )
    .collect()
}

fn output_info(terms: &Vec<Term>, morph_schemes: &Vec<MorphScheme>) {
    println!("Terms:");
    for t in terms.iter() {
      println!("    {}", t);
    }
    println!("");

    println!("Morph Schemes:");
    for m in morph_schemes.iter() {
      println!("    {}", m);
    }

    let start = start_nodes(terms);
    println!("Start nodes:");
    for m in start.iter() {
      println!("    {}", m);
    }
}


fn output_gv(terms: &Vec<Term>, morph_schemes: &Vec<MorphScheme>) {
    // let start = start_nodes(terms);
    let start = vec![Term::new("start", t_con("START"))];
    let edges_set: HashSet<Morphism> =
        edges_from_terms(&start.iter().collect(), &morph_schemes).take(1000).collect();

    fn format_dot_edge(m: &Morphism) -> String {
        // "((-> Domain) Domain)" -> "Domain" [ label = "&unit_domain" ]
        format!("\"{src}\" -> \"{tgt}\" [ label=\" {name} \" ]",
                src = m.source,
                tgt = m.target,
                name = m.name)
    }

    println!("digraph {{");
    println!("    node [ shape=point ] ");
    for m in edges_set {
        println!("    {}", format_dot_edge(&m));
    }
    println!("}}");
}

