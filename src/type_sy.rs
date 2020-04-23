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

impl fmt::Display for Kind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
       Kind::Star => write!(f, "*"),
       Kind::KFun(k1, k2) => write!(f, "({} -> {})", k1, k2),
    }
  }
}

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
    // Return Some((a,b)) if self is a function type (a -> b), None otherwise.
    pub fn fun_split(&self) -> Option<(&Type, &Type)> {
        match self {
            Type::TAp(l, r) => match &**l {
                Type::TAp(ll, lr) => match &**ll {
                    Type::TCon(Tycon(symbol, _)) => match &symbol[..] {
                        "->" => Some((lr,r)),
                        _ => None,
                    }
                    _ => None,
                }
                _ => None,
            }
            _ => None,
        }
    }

    // Return Ok(a) if self is a function type (a -> b), None otherwise
    pub fn fun_source(&self) -> Option<&Type> {
        self.fun_split().map(|(src, _)| src)
    }

    // Return Ok(b) if self is a function type (a -> b), None otherwise
    pub fn fun_target(&self) -> Option<&Type> {
        self.fun_split().map(|(_, tgt)| tgt)
    }

    // Returns (vec![a1, a2.., an], b) given a type a1 -> ... -> an -> b.
    pub fn split(&self) -> (Vec<&Type>, &Type) {
        let mut args_types = vec![];
        let mut cur_type = self;
        let mut fun_types = cur_type.fun_split();

        while fun_types.is_some() {
            let (src, tgt) = fun_types.unwrap();
            args_types.push(src);
            cur_type = tgt;
            fun_types = cur_type.fun_split();
        }

        (args_types, cur_type)
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
                        x => write!(f, "(({} {}) {})", x, lr, r),
                    }
                    _ => write!(f, "(({} {}) {})", ll, lr, r),
                }
                Type::TCon(Tycon(symbol, _)) => match &symbol[..] {
                    "[]" => write!(f, "[{}]", r),
                    x => write!(f, "({} {})", x, r),
                }
                _ => write!(f, "({} {})", l, r),
            }
            Type::TGen(i) => write!(f, "TGen {}", i),
        }
    }
}

//// Predefined types ////


//  tUnit    = TCon (Tycon "()" Star)
#[allow(dead_code)]
pub fn t_unit() -> Type {t_con("()")}

//  tChar    = TCon (Tycon "Char" Star)
#[allow(dead_code)]
pub fn t_char() -> Type {t_con("Char")}

//  t_integer = TCon (Tycon "Integer" Star)
#[allow(dead_code)]
pub fn t_integer() -> Type {t_con("Integer")}

//  t_int = TCon (Tycon "Int" Star)
#[allow(dead_code)]
pub fn t_int() -> Type {t_con("Int")}

//  t_nat = TCon (Tycon "Nat" Star)
#[allow(dead_code)]
pub fn t_nat() -> Type {t_con("Natural")}

//  tDouble  = TCon (Tycon "Double" Star)
#[allow(dead_code)]
pub fn t_double() -> Type {t_con("Double")}

//  tList    = TCon (Tycon "[]" (Kfun Star Star))
#[allow(dead_code)]
pub fn t_list() -> Type {
    Type::TCon(Tycon(
        String::from("[]"),
        Kind::KFun(
            Box::new(Kind::Star),
            Box::new(Kind::Star))))}

//  tArrow   = TCon (Tycon "(->)" (Kfun Star (Kfun Star Star)))
#[allow(dead_code)]
pub fn t_arrow() -> Type {
    Type::TCon(Tycon(
        String::from("->"),
        Kind::KFun(
            Box::new(Kind::Star),
            Box::new(Kind::KFun(
                Box::new(Kind::Star),
                Box::new(Kind::Star))))))}

//  tTuple2  = TCon (Tycon "(,)" (Kfun Star (Kfun Star Star)))
#[allow(dead_code)]
pub fn t_tuple_2() -> Type {
    Type::TCon(Tycon(
        String::from("(,)"),
        Kind::KFun(
            Box::new(Kind::Star),
            Box::new(Kind::KFun(
                Box::new(Kind::Star),
                Box::new(Kind::Star))))))}


//// Type constructor helpers ////

// Constant
pub fn t_con(name: &str) -> Type { Type::TCon(Tycon(String::from(name), Kind::Star)) }

// Variable with specified kind
pub fn t_var(name: &str, k: Kind) -> Type { Type::TVar(Tyvar(String::from(name), k)) }

// Variable with kind *
pub fn t_var_0(name: &str) -> Type { Type::TVar(Tyvar(String::from(name), Kind::Star)) }

// Parameterized data type
pub fn t_param(name: &str, xs: &[Type]) -> Type {
    fn go(name: &str, xs: &[Type], k: Kind) -> Type {
        if xs.is_empty() {
           Type::TCon(Tycon(String::from(name), k))
        } else {
           let tr = &xs[xs.len() - 1];
           let k_ = Kind::KFun(Box::new(tr.kind().clone()), Box::new(k));
           let tl = go(name, &xs[..xs.len() - 1], k_);
           Type::TAp(Box::new(tl), Box::new(tr.clone()))
        }
    }

    go(name, xs, Kind::Star)
}

// List
#[allow(dead_code)]
pub fn t_list_t(t: Type) -> Type {
   Type::TAp(Box::new(t_list()), Box::new(t))
}

// Tuple
#[allow(dead_code)]
pub fn t_pair(a: Type, b: Type) -> Type {
   Type::TAp(
       Box::new(Type::TAp(
           Box::new(t_tuple_2()),
           Box::new(a))),
       Box::new(b)
   )
}

// Function
#[allow(dead_code)]
pub fn t_fun(a: Type, b: Type) -> Type {
   Type::TAp(
       Box::new(Type::TAp(
           Box::new(t_arrow()),
           Box::new(a))),
       Box::new(b)
   )
}

// Function or Variable
#[allow(dead_code)]
pub fn t_fun_seq(xs: &[Type]) -> Type {
    match xs {
        [] => panic!("Vec xs should have at least 2 items"),
        [x] => x.clone(),
        [x, y] => t_fun(x.clone(), y.clone()),
        _ => t_fun(xs[0].clone(), t_fun_seq(&xs[1..])),
    }
}

// TGen
pub fn t_gen(i: usize) -> Type {Type::TGen(i)}


// Arity: 0 for type constants and variables, 1 for a type of function taking 1 argument, etc.
// Not to be confused with the kind.
// e.g.: a, a -> a, a -> a -> a all have kind * but their arity is respectively 0, 1, 2.
// TODO: what is the arity of a type with Kind * -> * or greater?
pub fn arity(t: &Type) -> u32 {
    t.fun_target().map_or(0, |tgt| 1 + arity(tgt))
}


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

// Type variable with kind *
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
                Kind::Star => panic!("I don't know the kind of {}.", t),
            }
            Type::TGen(_) => panic!("Cannot know the kind of TGen outside of a Scheme."),
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

// Return (a1, b1) where a1 and b1 are equivalenet to (a, b) up to
// a substitution of type variable names, and a1 and b1 share no
// variable name in common.
pub fn distinguish(a: &Type, b: &Type) -> (Type, Type) {
    let s_a = quantify(None, &a);
    let s_b = quantify(None, &b);

    let mut vn = VarNames::new();
    let a1 = fresh_inst(&s_a, &mut vn);
    let b1 = fresh_inst(&s_b, &mut vn);

    (a1, b1)
}

pub trait Types {
    fn apply_substitution(&self, subst: &Subst) -> Self;
    fn tv(&self) -> VecDeque<&Tyvar>;
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

pub fn var_names<T: Types>(t: &T) -> VecDeque<&String> {
    t.tv().iter().map(|&Tyvar(name, _)| name).collect()
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

impl fmt::Display for Scheme {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Scheme{{kinds: {:?}, t: {}}}", self.kinds, self.t)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_kind() {
        use Kind::*;
        assert_eq!(t_var_0("a").kind(), &Star);
        assert_eq!(t_param("A", &[t_var_0("a")]).kind(), &Star);
        assert_eq!(t_param("a", &[t_var_0("a"), t_var_0("b")]).kind(), &Star);
    }

    #[test]
    fn test_arity() {
        assert_eq!(arity(&t_var_0("a")), 0);
        assert_eq!(arity(&t_int()), 0);
        assert_eq!(arity(&t_fun(t_int(), t_int())), 1);
        assert_eq!(arity(&t_fun_seq(&[t_int(), t_int(), t_int()])), 2);
    }

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
