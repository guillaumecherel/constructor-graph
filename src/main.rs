use std::vec::Vec;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter;
use std::iter::Iterator;
use std::fmt;

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
enum Type {
  Nat,
  Int,
  Double,
  Text,
  Variable(String),
  Function(Box<Type>, Box<Type>),
}

impl Type {
    fn var(name: &str) -> Type {
        //OPTIM: changer String en &str pour éviter de créer un string à chaque fois.
       Type::Variable(String::from(name))
    }

    fn fun(source: Type, target: Type) -> Type {
       Type::Function(Box::new(source), Box::new(target))
    }


    // Renvoie les substitutions qui transforment self en to.
    //
    // bind C D bindings =
    //   si C == D alors Some bindings
    //   sinon None
    // bind a b bindings =
    //   si bindings(a) = b alors Just bindings
    //   sinon, si binsdigs(a) != b alors None
    //   sinon, si bindings(a) inexistant, alors Just (bindings ++ (a,b))
    //   pour tout a variables, b variable, constante ou fonction
    // bind (a -> b) (c -> d) bindings =
    //   bind b d (bind a c bindings)
    //   pour tout a b c d variable, constante ou fonction
    fn bindings(&self, to: &Type) -> Option<HashMap<Type, Type>> {
        fn go(this: &Type, to: &Type, mut bindings: HashMap<Type, Type>) -> Option<HashMap<Type, Type>>  {
            match (this, to) {
               (Type::Function(a, b), Type::Function(c, d)) =>
                   go(a, &c, bindings).and_then(|bindings_| go(b, &d, bindings_)),
               (Type::Variable(a), b) => {
                   let prev_pair = bindings.insert(Type::Variable(a.clone()), b.clone());
                   match prev_pair {
                       // bindings already had a value for Variable(a),
                       Some(prev_b) =>
                           if &prev_b == b {
                           // and it was equal to b, meaning that the two types are compatible
                           // without any additionnal binding.
                               Some(bindings)
                           } else {
                           // b is different from the previous binding for a, which means
                           // that the two types are incompatible.
                               None
                           },
                       // bindings didn't already have a value for Variable(a), which means that
                       // we can make the two types compatible by binding Variable(a) to b, which
                       // was done at the bindings.insert(...) statement above.
                       None => Some(bindings),
                   }
               }
               // At this point, a can only be a constant.
               (a, b) => if a == b {
                   Some(bindings)
               } else {
                   None
               }
            }
        }

        go(self, &to, HashMap::new())
    }

    // Replace the variables in self according to bindings.
    // If there is a variable in self which do not have any replacement and
    // have the same name as a variable being used as replacement, add a new
    // substitution for the first variable to an unused name.
    fn bind(&self, bindings: HashMap<Type, Type>) -> Type {
        // OPTIM: faut-il directement prendre un parame de type HashMap<&Type, &Type> en
        // paramètres plutôt que de créer cette collection ici?
        // All the type variables used as replacements.
        let replacements : HashSet<Type> = bindings.values().cloned().collect::<HashSet<Type>>();
        // Replacements' names.
        let names_in_replacements =
            replacements.iter().cloned().filter_map(|t: Type| -> Option<String> {
               match t {
                   Type::Variable(n) => Some(n),
                   _ => None,
               }
            });
        // New variable name candidates
        let candidates = &mut VarNames::new().exclude_all(names_in_replacements);
        
        fn go(
            x: &Type,
            mut substitutions: HashMap<Type, Type>,
            mut replacements: HashSet<Type>,
            candidates: &mut VarNames)
           -> (Type, HashMap<Type, Type>, HashSet<Type>)  {
            match x {
                Type::Variable(_) =>
                    match substitutions.get(&x) {
                        Some(y) => (y.clone(), substitutions, replacements),
                        None => if replacements.contains(&x) {
                            let new_name : String = candidates.next().expect("No new var name.");
                            let new_var = Type::Variable(new_name);
                            substitutions.insert(x.clone(), new_var.clone());
                            replacements.insert(new_var.clone());
                            (new_var, substitutions, replacements)
                        } else {
                            (x.clone(), substitutions, replacements)
                        }
                    }
                Type::Function(src, tgt) => {
                  let (src_, substitutions, replacements) =
                      go(src, substitutions, replacements, candidates);
                  let (tgt_, substitutions, replacements) =
                      go(tgt, substitutions, replacements, candidates);
                  (Type::fun(src_, tgt_), substitutions, replacements)
                }
                _ => (x.clone(), substitutions, replacements),
           }
        }

        let (x, _, _) = go(self, bindings, replacements, candidates);
        x
    }

    // Return the set of type variable names in self.
    fn variables(&self) -> HashSet<&Type> {
      match self {
        Type::Function(source, target) => {
            let mut a = source.variables();
            let b = target.variables();
            a.extend(&b);
            a
        }
        Type::Variable(_) => {
            let mut res = HashSet::new();
            res.insert(self);
            res
        }
        _ => HashSet::new(),
      }
    }

    // Return the set of type variable names in self.
    fn var_names(&self) -> HashSet<&String> {
      match self {
        Type::Function(source, target) => {
            let mut a = source.var_names();
            let b = target.var_names();
            a.extend(&b);
            a
        }
        Type::Variable(s) => {
            let mut res = HashSet::new();
            res.insert(s);
            res
        }
        _ => HashSet::new(),
      }
    }

}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::Nat => write!(f, "Nat"),
      Type::Int => write!(f, "Int"),
      Type::Double => write!(f, "Double"),
      Type::Text => write!(f, "Text"),
      Type::Variable(name) => write!(f, "{}", name),
      Type::Function(src, tgt) => write!(f, "({} -> {})", src, tgt),
    }
  }
}

#[cfg(test)]
mod tests_type {
    use super::*;

    #[test]
    fn test_var_names() {
        let f = Type::fun(
            Type::fun( Type::var("a"), Type::var("b")),
            Type::var("c"));
        let result : HashSet<String> = f.var_names().into_iter().cloned().collect();
        let expected : HashSet<String> =
            vec!["a", "b", "c"].into_iter().map(|s:&str| -> String { String::from(s) }).collect();
        assert_eq!(result, expected)
    }

    #[test]
    fn test_bindings() {
        let t1 = Type::fun(Type::var("a"), Type::fun(Type::Nat, Type::var("a")));
        let t2 = Type::fun(Type::Int, Type::fun(Type::Nat, Type::Int));
        let result : Option<HashMap<Type, Type>> = t1.bindings(&t2);
        let expected : Option<HashMap<Type, Type>> = Some(
             vec![(Type::var("a"), Type::Int)].into_iter().collect()
         );
        assert_eq!( result, expected);

        let t1 = Type::fun(Type::var("a"), Type::fun(Type::Nat, Type::var("b")));
        let t2 = Type::fun(Type::fun(Type::Nat, Type::Int), Type::fun(Type::Nat, Type::Int));
        let result : Option<HashMap<Type, Type>> = t1.bindings(&t2);
        let expected : Option<HashMap<Type, Type>> = Some(
             vec![(Type::var("a"), Type::fun(Type::Nat, Type::Int)),
                  (Type::var("b"), Type::Int)]
             .into_iter().collect()
         );
        assert_eq!( result, expected);

        let t1 = Type::fun(Type::var("a"), Type::fun(Type::Nat, Type::var("a")));
        let t2 = Type::fun(Type::Int, Type::fun(Type::Nat, Type::Nat));
        let result : Option<HashMap<Type, Type>> = t1.bindings(&t2);
        let expected : Option<HashMap<Type, Type>> = None;
        assert_eq!( result, expected);
    }

    #[test]
    fn test_bind() {
        let t = Type::Nat;
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.clone().bind(bindings);
        assert_eq!(result, t);

        let t = Type::var("a");
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::var("b");
        assert_eq!(result, expect);

        let t = Type::fun(Type::var("a"), Type::var("b"));
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::fun(Type::var("b"), Type::var("a"));
        assert_eq!(result, expect);

        let t = Type::fun(
            Type::fun(Type::var("a"), Type::var("b")),
            Type::var("b"));
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::fun(
            Type::fun(Type::var("b"), Type::var("a")),
            Type::var("a"));
        assert_eq!(result, expect);

        let t = Type::fun(
            Type::fun(Type::var("a"), Type::var("b")),
            Type::var("c"));
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::fun(
            Type::fun(Type::var("b"), Type::var("a")),
            Type::var("c"));
        assert_eq!(result, expect);

        let t = Type::fun(
            Type::var("a"),
            Type::fun(Type::var("b"), Type::var("c")));
        let bindings: HashMap<Type, Type> = vec![(Type::var("a"), Type::var("b"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::fun(
            Type::var("b"),
            Type::fun(Type::var("a"), Type::var("c")));
        assert_eq!(result, expect);

        let t = Type::fun(
            Type::fun(Type::var("d"), Type::var("b")),
            Type::fun(Type::var("b"), Type::var("c")));
        let bindings: HashMap<Type, Type> =
            vec![(Type::var("c"), Type::var("d")),
                 (Type::var("b"), Type::var("c"))]
            .into_iter().collect();
        let result = t.bind(bindings);
        let expect = Type::fun(
            Type::fun(Type::var("a"), Type::var("c")),
            Type::fun(Type::var("c"), Type::var("d")));
        assert_eq!(result, expect);
    }
}

#[derive(Clone)]
struct VarNames {
    value: String,
    excluded: HashSet<String>
}

impl VarNames {
    fn new() -> VarNames {
        VarNames {
            value: String::from(""),
            excluded: HashSet::new()
        }
    }

    fn exclude(mut self, name: String) -> VarNames {
        self.excluded.insert(name);
        self
    }

    fn exclude_all<T>(mut self, names: T) -> VarNames
        where T: Iterator<Item = String>
    {
        self.excluded.extend(names);
        self
    }
}

impl Iterator for VarNames {
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

#[cfg(test)]
mod tests_var_names {
    use super::*;

    #[test]
    fn test_excluding() {
        let f = Type::fun(
            Type::fun( Type::var("a"), Type::var("b")),
            Type::var("d"));
        let next_3 : Vec<String> = VarNames::new().exclude_all(f.var_names().into_iter().cloned()).into_iter().take(3).collect();
        let expected : Vec<String> = vec!(String::from("c"), String::from("e"), String::from("f"));
        assert_eq!(next_3, expected);
    }
}

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
            target : target
        }
    }
    
    // Create a morphism (.x): ((a -> b) -> b) from the given term x: a such that (.x) g = g x.
    fn ap(Term(label, typ): &Term) -> Morphism {
      let used_var_names = typ.var_names().into_iter().cloned();
      let mut candidates = VarNames::new().exclude_all(used_var_names);
      let nvn = Type::Variable(candidates.next().expect("No available var name."));
      Morphism {
        name: [".", &label].concat(),
        source: Type::Function(Box::new(typ.clone()), Box::new(nvn.clone())),
        target: nvn,
      }
    }

    // Create a morphism f: a -> b from a function term a -> b. Return None if the given
    // term is not a function.
    fn from_function(Term(label, typ): &Term) -> Option<Morphism> {
       match typ {
         Type::Function(a, b) => Some(Morphism{
             name: label.clone(),
             source: *a.clone(),
             target: *b.clone()
         }),
         _ => None,
       }
    }

    fn bind_source(&self, to: &Type) -> Option<Morphism> {
        self.source.bindings(to).map(|bindings| {
            Morphism {
                name: self.name.clone(),
                source: to.clone(),
                target: self.target.bind(bindings)
            }
        })
    }

    fn chain_forward() -> Morphism {
        Morphism {
            name: String::from(">"),
            source: Type::fun(Type::var("a"), Type::var("b")),
            target: Type::fun(
                Type::fun(Type::var("b"), Type::var("c")),
                Type::fun(Type::var("a"), Type::var("c"))
            )
        }
    }

    fn chain_backward() -> Morphism {
        Morphism {
            name: String::from("<"),
            source: Type::fun( Type::var("b"), Type::var("c") ),
            target: Type::fun(
                Type::fun( Type::var("a"), Type::var("b") ),
                Type::fun( Type::var("a"), Type::var("c") )
            ),
        }
    }
}



impl fmt::Display for Morphism {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Morphism{name, source, target} => write!(f, "{}: {} -> {}", name, source, target),
    }
  }
}


#[cfg(test)]
mod tests_morphism {
    use super::*;

    #[test]
    fn test_bind_source() {
       let m = Morphism{
           name: String::from("f"),
           source: Type::var("a"),
           target: Type::var("a")
       };
       let to = Type::var("b");
       let result = m.bind_source(&to);
       let expect = Some(Morphism{
           name: String::from("f"),
           source: Type::var("b"),
           target: Type::var("b")}
       );
       assert_eq!(result, expect);

       let m = Morphism{
           name: String::from("f"),
           source: Type::var("a"),
           target: Type::var("b")
       };
       let to = Type::var("b");
       let result = m.bind_source(&to);
       let expect = Some(Morphism{
           name: String::from("f"),
           source: Type::var("b"),
           target: Type::var("a")}
       );
       assert_eq!(result, expect);

       let m = Morphism{
           name: String::from("f"),
           source: Type::fun(Type::var("b"), Type::var("c")),
           target: Type::fun(
               Type::fun(Type::var("a"), Type::var("b")),
               Type::fun(Type::var("a"), Type::var("c")))
       };
       let to = Type::fun(Type::var("x"), Type::var("y"));
       let result = m.bind_source(&to);
       let expect = Some(Morphism{
           name: String::from("f"),
           source: Type::fun(Type::var("x"), Type::var("y")),
           target: Type::fun(
               Type::fun(Type::var("a"), Type::var("x")),
               Type::fun(Type::var("a"), Type::var("y")))
       });
       assert_eq!(result, expect);
    }
}

fn morphisms_from_terms(terms: &Vec<Term>) -> Vec<Morphism> {
      terms.iter().map(|t| Morphism::ap(t))
      .chain(terms.iter().filter_map(|t| Morphism::from_function(t)))
      .chain(iter::once(Morphism::chain_forward()))
      .chain(iter::once(Morphism::chain_backward()))
      .collect()
}


fn edges(n: &Type, morphisms: &Vec<Morphism>) -> Vec<Morphism> {
   morphisms.iter().filter_map(|m: &Morphism| -> Option<Morphism> {
       m.bind_source(n)
   }).collect()
}


#[cfg(test)]
mod tests_edges {
    use super::*;

    #[test]
    fn test_edges() {
        let terms: Vec<Term> = vec!
          [ Term::new("1", Type::Nat)
          , Term::new("1", Type::Int)
          , Term::new("f", Type::fun(Type::Nat,Type::Int))
          , Term::new("g", Type::fun(Type::var("a"), Type::var("b")))
          ];

        let morphisms = morphisms_from_terms(&terms);

        let n = Type::Nat;
        assert_eq!(
            edges(&n, &morphisms),
            vec![Morphism::new("f", Type::Nat, Type::Int),
                 Morphism::new("g", Type::Nat, Type::var("b"))]
        );

        let n = Type::fun(Type::var("a"), Type::var("b"));
        assert_eq!(
            edges(&n, &morphisms),
            vec![Morphism::new("g", Type::fun(Type::var("a"), Type::var("b")), Type::var("b")),
                 Morphism::new(">",
                     Type::fun(Type::var("a"), Type::var("b")),
                     Type::fun(
                         Type::fun(Type::var("b"), Type::var("c")),
                         Type::fun(Type::var("a"), Type::var("c"))
                     )
                 ),
                 Morphism::new("<",
                     Type::fun(Type::var("a"), Type::var("b")),
                     Type::fun(
                         Type::fun(Type::var("c"), Type::var("a")),
                         Type::fun(Type::var("c"), Type::var("b"))
                     )
                 )
             ]
        );

        let n = Type::fun(Type::Int, Type::Int);
        assert_eq!(
            edges(&n, &morphisms),
            vec![Morphism::new(".1", Type::fun(Type::Int, Type::Int), Type::Int),
                 Morphism::new("g", Type::fun(Type::Int, Type::Int), Type::var("b")),
                 Morphism::new(">",
                     Type::fun(Type::Int, Type::Int),
                     Type::fun(
                         Type::fun(Type::Int, Type::var("c")),
                         Type::fun(Type::Int, Type::var("c"))
                     )
                 ),
                 Morphism::new("<",
                     Type::fun(Type::Int, Type::Int),
                     Type::fun(
                         Type::fun(Type::var("a"), Type::Int),
                         Type::fun(Type::var("a"), Type::Int)
                     )
                 )
             ]
        );
    }
}


fn main() {

  let terms: Vec<Term> = vec!
      [ Term::new("1", Type::Nat)
      , Term::new("1", Type::Int)
      , Term::new("f", Type::fun(Type::Nat,Type::Int))
      , Term::new("g", Type::fun(Type::var("a"), Type::var("b")))
      ];

  for t in terms.iter() {
    println!("Term: {}", t);
  }

  let morphisms = morphisms_from_terms(&terms);

  for m in morphisms.iter() {
    println!("Morphism: {}", m);
  }

}
