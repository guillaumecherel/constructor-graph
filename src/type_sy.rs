// The type system in this module is drawn from https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html#tthFtNtAAB
// Reference:
// Typing Haskell in Haskell
// MARK P. JONES
// Pacific Software Research Center
// Department of Computer Science and Engineering
// Oregon Graduate Institute of Science and Technology
// 20000 NW Walker Road, Beaverton, OR 97006, USA
// mpj@cse.ogi.edu
// Version of November 23, 2000.

#![allow(dead_code)]

use std::vec::Vec;
use std::collections::VecDeque;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::Iterator;
use std::fmt;

use crate::util::union;

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
pub enum Kind {
    Star,
    KFun(Box<Kind>, Box<Kind>),
}

// impl fmt::Display for Kind {
//   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//     match self {
//        Star => write!(f, "*"),
//        KFun(k1, k2) => write!(f, "({} -> {})", k1, k2),
//     }
//   }
// }

// impl fmt::Display for Vec<Kind> {
//   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//       if self.is_empty {write!(f, "]")}
//       else {write }
//   }
// }


#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
pub enum Type {
  TCon(Tycon),
  TVar(Tyvar),
  TAp(Box<Type>, Box<Type>),
  TGen(usize),
}

impl Type {
    // Return Some(a) if self is a function type (a -> b), None otherwise
    pub fn source(&self) -> Result<&Type, String> {
       match &self {
           Type::TAp(ap, _) =>
             match &**ap {
               Type::TAp(_, s) => Ok(&s),
               _ => Err(String::from("Type is probably not a function")),
             }
           _ => Err(String::from("Type is probably not a function")),
       }
    }

    pub fn target(&self) -> Option<&Type> {
       match &self {
           Type::TAp(_, t) => Some(&t),
           _ => None,
       }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::TCon(tc) => write!(f, "{}", tc),
            Type::TVar(u) => write!(f, "{}", u),
            Type::TAp(l, r) => match &**l {
                Type::TAp(ll, lr) => match &**ll {
                    Type::TCon(Tycon(symbol, _)) => match &symbol[..] {
                        "->" => write!(f, "({} -> {})", lr, r),
                        "(,)"=> write!(f, "({}, {})", lr, r),
                        _ => panic!("I don't know how to format {:?}", self),
                    }
                    _ => panic!("I don't know how to format {:?}", self),
                }
                Type::TCon(Tycon(symbol, _)) => match &symbol[..] {
                    "[]" => write!(f, "[{}]", r.to_string()),
                    _ => panic!("I don't know how to format {:?}", self),
                }
                _ => panic!("I don't know how to format {:?}", self),
            }
            Type::TGen(i) => write!(f, "TGen {}", i),
        }
    }
}

//  tUnit    = TCon (Tycon "()" Star)
pub fn t_unit() -> Type {Type::TCon(Tycon(String::from("()"), Kind::Star))}
//  tChar    = TCon (Tycon "Char" Star)
pub fn t_char() -> Type {Type::TCon(Tycon(String::from("Char"), Kind::Star))}
//  t_integer = TCon (Tycon "Integer" Star)
pub fn t_integer() -> Type {Type::TCon(Tycon(String::from("Integer"), Kind::Star))}
//  t_int = TCon (Tycon "Int" Star)
pub fn t_int() -> Type {Type::TCon(Tycon(String::from("Int"), Kind::Star))}
//  t_nat = TCon (Tycon "Nat" Star)
pub fn t_nat() -> Type {Type::TCon(Tycon(String::from("Natural"), Kind::Star))}
//  tDouble  = TCon (Tycon "Double" Star)
pub fn t_double() -> Type {Type::TCon(Tycon(String::from("Double"), Kind::Star))}

//  tList    = TCon (Tycon "[]" (Kfun Star Star))
pub fn t_list() -> Type {Type::TCon(Tycon(String::from("[]"), Kind::KFun(Box::new(Kind::Star), Box::new(Kind::Star))))}
//  tArrow   = TCon (Tycon "(->)" (Kfun Star (Kfun Star Star)))
pub fn t_arrow() -> Type {
    Type::TCon(Tycon(
        String::from("->"),
        Kind::KFun(
            Box::new(Kind::Star),
            Box::new(Kind::KFun(
                Box::new(Kind::Star),
                Box::new(Kind::Star))
            )
        )
    ))
}
//  tTuple2  = TCon (Tycon "(,)" (Kfun Star (Kfun Star Star)))
pub fn t_tuple_2() -> Type {
    Type::TCon(Tycon(
        String::from("(,)"),
        Kind::KFun(
            Box::new(Kind::Star),
            Box::new(Kind::KFun(
                Box::new(Kind::Star),
                Box::new(Kind::Star))
            )
        )
    ))
}

pub fn t_con(name: &str) -> Type { Type::TCon(Tycon(String::from(name), Kind::Star)) }

// tVar with kind Star.
pub fn t_var_0(name: &str) -> Type { Type::TVar(Tyvar(String::from(name), Kind::Star)) }

// tVar with Kind
pub fn t_var(name: &str, k: Kind) -> Type { Type::TVar(Tyvar(String::from(name), k)) }

// Full list type
pub fn t_list_t(t: Type) -> Type {
   Type::TAp(Box::new(t_list()), Box::new(t))
}

// Tuple
pub fn t_pair(a: Type, b: Type) -> Type {
   Type::TAp(
       Box::new(Type::TAp(
           Box::new(t_tuple_2()),
           Box::new(a))),
       Box::new(b)
   )
}

// t_fun
pub fn t_fun(a: Type, b: Type) -> Type {
   Type::TAp(
       Box::new(Type::TAp(
           Box::new(t_arrow()),
           Box::new(a))),
       Box::new(b)
   )
}

// Arity: 0 for type constants and variables, 1 for a type of function taking 1 argument, etc.
// Not to be confused with the kind.
// e.g.: a, a -> a, a -> a -> a all have kind Star but their arity is respectively 0, 1, 2.
// TODO: what is the arity of a type with Kind * -> * or greater?
pub fn arity(t: &Type) -> u32 {
    match t {
       Type::TCon(Tycon(_, Kind::Star)) => 0,
       Type::TVar(Tyvar(_, Kind::Star)) => 0,
       Type::TAp(l, r) => if t.kind() == &Kind::Star {
           1 + arity(r)
       } else {
           panic!("Not sure how to compute arity for {:?}", t)
       },
       _ => panic!("Not sure how to compute arity for {:?}", t),
    }
}

#[cfg(test)]
mod tests_arity {
    use super::*;

    #[test]
    fn test_arity() {
        assert_eq!(arity(&t_var_0("a")), 0);
        assert_eq!(arity(&t_int()), 0);
        assert_eq!(arity(&t_fun(t_int(), t_int())), 1);
        assert_eq!(arity(&t_fun_seq(&[t_int(), t_int(), t_int()])), 2);
    }
}

pub fn t_fun_seq(xs: &[Type]) -> Type {
    match xs {
        [] => panic!("Vec xs should have at least 2 items"),
        [_] => panic!("Vec xs should have at least 2 items"),
        [x, y] => t_fun(x.clone(), y.clone()),
        _ => t_fun(xs[0].clone(), t_fun_seq(&xs[1..])),
    }
}

//t_gen
pub fn t_gen(i: usize) -> Type {Type::TGen(i)}

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
pub struct Tycon(String, Kind);

impl fmt::Display for Tycon {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Tycon(name, _) => write!(f, "{}", name),
    }
  }
}

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
pub struct Tyvar(String, Kind);

impl fmt::Display for Tyvar {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Tyvar(name, _) => write!(f, "{}", name),
    }
  }
}

// Type variable arity 0
pub fn ty_var_0(name: &str) -> Tyvar {Tyvar(String::from(name), Kind::Star)}

pub trait HasKind {
    fn kind(&self) -> &Kind;
}

impl HasKind for Tyvar {
    fn kind(&self) -> &Kind {
        match self { Tyvar(_, k) => &k }
    }
}

impl HasKind for Tycon {
    fn kind(&self) -> &Kind {
        match self { Tycon(_, k) => &k }
    }
}

impl HasKind for Type {
    fn kind(&self) -> &Kind {
        match self {
            Type::TCon(tc) => tc.kind(),
            Type::TVar(u) => u.kind(),
            Type::TAp(t, _) => match t.kind() {
                Kind::KFun(_, k) => k,
                Kind::Star => panic!("Code shouldn't pass here."),
            }
            Type::TGen(_) => panic!("Code shouldn't pass here: cannot know the kind of TGen outside of a Scheme."),
        }
    }
}

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
pub struct Subst(HashMap<Tyvar, Type>);

impl fmt::Display for Subst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Subst(hmap) = self;
        for (tv, t) in hmap.iter() {
           write!(f, "{} ~> {}\n", tv, t)?;
        }
        Ok(())
    }
}
    
impl Subst {
    fn null() -> Subst {Subst(HashMap::new())}

    fn from_iter<T>(t: T) -> Subst where
        T: Iterator<Item=(Tyvar, Type)> {
        Subst(t.collect())
    }

    fn single(u: Tyvar, t: Type) -> Subst {
        let mut hm = HashMap::new();
        hm.insert(u, t);
        Subst(hm)
    }

    fn insert(&mut self, u: Tyvar, t: Type) {
        let mut hm = HashMap::new();
        hm.insert(u, t);
    }

    fn get(&self, u: &Tyvar) -> Option<&Type> {
       match self {Subst(m) => m.get(u)}
    }

    // Perform s @@ self
    fn chain(mut self, mut s: Subst) -> Subst {
       // Update all substitutions in self with those of s then take the union.
       for (_, t) in self.0.iter_mut() {
            *t = t.apply_substitution(&s);
       }
       // If self and s contain substitutions for the same variable,
       // we want to keep the substitution in self updated with the substitutions
       // from s. e.g.: if self contains a ~> b and s contains a ~> c and b ~> d,
       // we want the result to contain a ~> d and b ~> d.
       s.0.extend(self.0.into_iter());
       s
    }
}

pub trait Types {
    fn apply_substitution(&self, subst: &Subst) -> Self;
    fn tv(&self) -> VecDeque<&Tyvar>;
}

pub fn var_names<T: Types>(t: &T) -> VecDeque<&String> {
    t.tv().iter().map(|&Tyvar(name, _)| name).collect()
}

impl Types for Type {
    fn apply_substitution(&self, subst: &Subst) -> Self {
        match self {
            Type::TVar(u) => match subst.get(u) {
                Some(t) => t.clone(),
                None => Type::TVar(u.clone()),
            },
            Type::TAp(l, r) =>
                Type::TAp(Box::new(l.apply_substitution(subst)),
                          Box::new(r.apply_substitution(subst))),
            t => t.clone(),
        }
    }

    fn tv(&self) -> VecDeque<&Tyvar> {
        match self {
            Type::TVar(u) => {
                let mut hs = VecDeque::new();
                hs.push_back(u);
                hs
            },
            Type::TAp(l, r) => {
                union(l.tv(), r.tv())
            }
            _ => VecDeque::new(),
        }
    }
}

pub fn mgu(a: &Type, b: &Type) -> Result<Subst, String> {
    match (a, b) {
        (Type::TAp(l, r), Type::TAp(l_, r_)) =>
            mgu(l, l_)
            .and_then(|s1|
                mgu(&r.apply_substitution(&s1), &r_.apply_substitution(&s1))
                .and_then(|s2| Ok(s1.chain(s2)))
            ),
        (Type::TVar(u), t) => var_bind(u, t),
        (t, Type::TVar(u)) => var_bind(u, t),
        (Type::TCon(tc1), Type::TCon(tc2)) =>
            if tc1 == tc2 {Ok(Subst::null())}
            else {Err(format!("types do not unify: Type 1 = {:?}, Type 2 = {:?}", a, b))},
        (_, _) => Err(format!("types do not unify: Type 1 = {:?}, Type 2 = {:?}", a, b)),
    }
}

fn var_bind(u: &Tyvar, t: &Type) -> Result<Subst, String> {
    if match t {Type::TVar(v) => v == u, _ => false } {
       Ok(Subst::null())
    } else if t.tv().contains(&u) {
       Err(format!("occurs check fails: the variable {:?} occurs in the type {:?}", u, t))
    } else if u.kind() != t.kind() {
       Err(format!("kinds do not match: Type 1 = {:?}, Type 2 = {:?}", t, u))
    } else {
       Ok(Subst::single(u.clone(), t.clone()))
    }
}

#[cfg(test)]
mod tests_mgu {
    use super::*;

    #[test]
    fn test_mgu() {
        // a -> (Nat -> a)
        let t1 = t_fun(t_var_0("a"), t_fun(t_nat(), t_var_0("a")));
        // Integer -> (Nat -> Integer)
        let t2 = t_fun(t_integer(), t_fun(t_nat(), t_integer()));
        let result : Result<Subst, String> = mgu(&t1, &t2);
        let expected : Result<Subst, String> = Ok(
             Subst(vec![(ty_var_0("a"), t_integer())].into_iter().collect())
         );
        assert_eq!( result, expected);

        // a -> (Nat -> b)
        let t1 = t_fun(t_var_0("a"), t_fun(t_nat(), t_var_0("b")));
        // (Nat -> Int) -> (Nat -> Int)
        let t2 = t_fun(t_fun(t_nat(), t_integer()), t_fun(t_nat(), t_integer()));
        let result : Result<Subst, String> = mgu(&t1, &t2);
        let expected : Result<Subst, String> = Ok(
             Subst(vec![(ty_var_0("a"), t_fun(t_nat(), t_integer())),
                  (ty_var_0("b"), t_integer())]
             .into_iter().collect())
         );
        assert_eq!( result, expected);

        // a -> (Nat -> a)
        let t1 = t_fun(t_var_0("a"), t_fun(t_nat(), t_var_0("a")));
        // Integer -> (Nat -> Nat)
        let t2 = t_fun(t_integer(), t_fun(t_nat(), t_nat()));
        let result : Result<Subst, String> = mgu(&t1, &t2);
        assert!( result.is_err() );
    }

    // #[test]
    // fn test_bind() {
    //     let t = Type::Nat;
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.clone().bind(bindings);
    //     assert_eq!(result, t);

    //     let t = Type::var("a");
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::var("b");
    //     assert_eq!(result, expect);

    //     let t = Type::funtyvar0(Type::var("a"), Type::var("b"));
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::fun(Type::var("b"), Type::var("a"));
    //     assert_eq!(result, expect);

    //     let t = Type::fun(
    //         Type::fun(Type::var("a"), Type::var("b")),
    //         Type::var("b"));
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::fun(
    //         Type::fun(Type::var("b"), Type::var("a")),
    //         Type::var("a"));
    //     assert_eq!(result, expect);

    //     let t = Type::fun(
    //         Type::fun(Type::var("a"), Type::var("b")),
    //         Type::var("c"));
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::fun(
    //         Type::fun(Type::var("b"), Type::var("a")),
    //         Type::var("c"));
    //     assert_eq!(result, expect);

    //     let t = Type::fun(
    //         Type::var("a"),
    //         Type::fun(Type::var("b"), Type::var("c")));
    //     let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::fun(
    //         Type::var("b"),
    //         Type::fun(Type::var("a"), Type::var("c")));
    //     assert_eq!(result, expect);

    //     let t = Type::fun(
    //         Type::fun(Type::var("d"), Type::var("b")),
    //         Type::fun(Type::var("b"), Type::var("c")));
    //     let bindings: HashMap<Type, Type> =
    //         vec![(Type::var("c"), Type::var("d")),
    //              (Type::var("b"), Type::var("c"))]
    //         .into_iter().collect();
    //     let result = t.bind(bindings);
    //     let expect = Type::fun(
    //         Type::fun(Type::var("a"), Type::var("c")),
    //         Type::fun(Type::var("c"), Type::var("d")));
    //     assert_eq!(result, expect);
    // }
}


#[derive(Clone)]
pub struct VarNames<'a> {
    value: String,
    excluded: HashSet<&'a String>
}

impl<'a> VarNames<'a> {
    pub fn new() -> VarNames<'a> {
        VarNames {
            value: String::from(""),
            excluded: HashSet::new()
        }
    }

    pub fn excluding<T>(names: T) -> VarNames<'a>
        where T: Iterator<Item=&'a String> {
        VarNames {
            value: String::from(""),
            excluded: names.collect(),
        }
    }

    pub fn exclude(mut self, name: &'a String) -> VarNames<'a> {
        self.excluded.insert(name);
        self
    }

    pub fn exclude_all<T>(mut self, names: T) -> VarNames<'a>
        where T: Iterator<Item = &'a String>
    {
        self.excluded.extend(names);
        self
    }
}

impl<'a> Iterator for VarNames<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next : String = next_string(&self.value);
        while self.excluded.contains(&next) {
            next = next_string(&next);
        }
        self.value = next;
        Some(self.value.clone())
    }
}

fn next_string(s: &str) -> String {
  match s.chars().rev().next() {
    None => String::from("a"),
    Some('z') => {
      let mut t = next_string(&s[..s.len() - 1]);
      t.push('a');
      t
    }
    Some(c) => {
      let mut t = String::from(&s[..s.len() - 1]);
      t.push((c as u8 + 1) as char);
      t
    }
  }
}

// #[cfg(test)]
// mod tests_var_names {
//     use super::*;
// 
//     #[test]
//     fn test_excluding() {
//         let f = Type::fun(
//             Type::fun( Type::var("a"), Type::var("b")),
//             Type::var("d"));
//         let next_3 : Vec<String> = VarNames::new().exclude_all(f.var_names().into_iter().cloned()).into_iter().take(3).collect();
//         let expected : Vec<String> = vec!(String::from("c"), String::from("e"), String::from("f"));
//         assert_eq!(next_3, expected);
//     }
// }


// This is a simplified version of the Scheme definition that appears in the reference paper
// that doesn't take into account typeclasses: as a result,
// Qual Type is simply replaced by Type.
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
pub struct Scheme {
    pub kinds: Vec<Kind>,
    pub t: Type,
}

impl fmt::Display for Scheme {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Scheme{{kinds: {:?}, t: {}}}", self.kinds, self.t)
  }
}

// If vs is None, quantify all type variables in t.
pub fn quantify(vs: Option<Vec<Tyvar>>, t: &Type) -> Scheme {
    let vs_ : VecDeque<&Tyvar> = match vs {
        None => t.tv(),
        Some(vs) => t.tv().into_iter().filter(|v| vs.contains(v)).collect(),
    };
    let ks : Vec<Kind> = vs_.iter().map(|&v| v.kind()).cloned().collect();
    let s : Subst = Subst::from_iter(vs_.into_iter().cloned().zip((0..).into_iter().map(t_gen)));
    
    Scheme {
        kinds: ks,
        t: t.apply_substitution(&s),
    }
}


impl Types for Scheme {
    fn apply_substitution(&self, subst: &Subst) -> Self {
       Scheme {
           kinds: self.kinds.clone(),
           t: self.t.apply_substitution(subst),
       }
    }

    fn tv(&self) -> VecDeque<&Tyvar> {
       self.t.tv()
    }
}

fn new_t_var(k: Kind, names: &mut VarNames) -> Type {
    let new_name = names.next().expect("No new var name");
    t_var(&new_name, k)
}

pub fn fresh_inst(s: &Scheme, names: &mut VarNames) -> Type {
    let ts : Vec<Type> = s.kinds.iter().cloned().map(|k| new_t_var(k, names)).collect();
    s.t.inst(&ts)
}

#[cfg(test)]
mod tests_scheme {
    use super::*;

    #[test]
    fn test_quantify() {
        // Integer -> (Nat -> Integer)
        let t = t_fun(t_integer(), t_fun(t_nat(), t_integer()));
        let s = quantify(None, &t);
        let e = Scheme {
               kinds : vec![],
               t : t.clone(),
        };
        assert_eq!(s, e);

        // a -> (Nat -> a)
        let t = t_fun(t_var_0("a"), t_fun(t_nat(), t_var_0("a")));
        let s = quantify(None, &t);
        let e = Scheme {
               kinds : vec![Kind::Star],
               t : t_fun(t_gen(0), t_fun(t_nat(), t_gen(0))),
        };
        assert_eq!(s, e);

        // a -> b
        let t = t_fun(t_var_0("a"), t_var_0("b"));
        let s = quantify(None, &t);
        let e = Scheme {
               kinds : vec![Kind::Star, Kind::Star],
               t : t_fun(t_gen(0),  t_gen(1)),
        };
        assert_eq!(s, e);

        // (g -> e) -> (d -> b)
        let t = t_fun(t_fun(t_var_0("g"), t_var_0("e")), t_fun(t_var_0("d"), t_var_0("b")));
        let s = quantify(None, &t);
        let e = Scheme {
               kinds : vec![Kind::Star, Kind::Star, Kind::Star, Kind::Star],
               t : t_fun(t_fun(t_gen(0), t_gen(1)), t_fun(t_gen(2), t_gen(3))),
        };
        assert_eq!(s, e);

    }

    #[test]
    fn test_fresh_inst() {
        let mut candidates = VarNames::new();
        let sch = Scheme {
               kinds : vec![Kind::Star, Kind::Star],
               t : t_fun(t_fun(t_gen(0), t_gen(1)), t_gen(1)),
        };
        let i = fresh_inst(&sch, &mut candidates);
        let expect = t_fun(t_fun(t_var_0("a"), t_var_0("b")), t_var_0("b"));
        assert_eq!(i, expect);
    }
}


pub trait Instantiate {
    fn inst(&self, ts: &Vec<Type>) -> Self;
}

impl Instantiate for Type {
    fn inst(&self, ts:&Vec<Type>) -> Self {
        match self {
            Type::TAp(l, r) =>
                Type::TAp(Box::new(l.inst(ts)),
                          Box::new(r.inst(ts))),
            Type::TGen(n) => ts[*n].clone(),
            t => t.clone(),
        }
    }
}
