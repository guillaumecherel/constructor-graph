#![allow(dead_code)]

use std::collections::VecDeque;
use std::fmt::Display;

// Duplicates and elements of the first list, are removed from the
// the second list, but if the first list contains duplicates, so will
// the result.
pub fn union<T: Eq>(mut xs: VecDeque<T>, ys: VecDeque<T>) -> VecDeque<T> {
    xs.extend(delete(&xs, nub(ys)));
    xs
}

// Removes duplicate elements from a list.
pub fn nub<T: Eq>(mut xs: VecDeque<T>) -> VecDeque<T> {
    match xs.pop_front() {
        None => xs,
        Some(x) => {
            let mut xs2 = nub(xs.into_iter().filter(|y| x != *y).collect());
            xs2.push_front(x);
            xs2
        }
    }
}

// remove from ys all elements in xs
pub fn delete<T: Eq>(xs: &VecDeque<T>, ys: VecDeque<T>) -> VecDeque<T> {
    ys.into_iter().filter(|y| !xs.contains(y)).collect()
}

pub fn vec_to_string<T: Display>(v: &Vec<T>, sep: &str) -> String {
    v.iter().map(|x| x.to_string()).fold(String::from("["), |acc, x| acc + sep + &x) + "]"
}

// struct Parser<T>(T);
// 
// impl<T> Parser<T>
// {
//    fn run<I, U>(self, it: I) -> Result<U, String>
//    where
//       T: FnOnce(I) -> Result<U, String>,
//       I: Iterator<Item = char>,
//    {
//        match self { Parser(p) => p(it) }
//    }
// 
//    fn map<I, U, F,V>(self, f: F) -> Parser<V>
//    where
//       F: FnOnce(U) -> V,
//       T: FnOnce(I) -> Result<U, String>,
//       I: Iterator<Item = char>,
//    {
//        match self { Parser(p) => { Parser(|it| p(it).map(f)) } }
//    }
// 
//    fn and_then<F, V>(self, f: F) -> Parser<V>
//    where F: FnOnce(U) -> Parser<V>
//    {
//        match self { Parser(p) =>
//            Parser(|it| match p(it).map(f) {
//                 Ok(Parser(x)) => Ok(x),
//                 e => e,
//                 
//                 })
//        }
//    }
// 
// }
// 
// struct CheckPoint<I, T>
// {
//     save: Vec<T>,
//     it: I,
// }
// 
// impl<I, T> CheckPoint<I, T>
// where
//     I: Iterator<Item=T>,
//     T: Clone,
// {
//     fn new(it: I) -> CheckPoint<I, T> {
//        CheckPoint{
//           save: Vec::new(),
//           it: it,
//        }
//     }
//     
//     fn restore(self) -> iter::Chain<vec::IntoIter<T>, I> {
//        self.save.into_iter().chain(self.it)
//     }
// }
// 
// impl<I, T> Iterator for CheckPoint<I, T>
// where
//     I: Iterator<Item=T>,
//     T: Clone,
// {
//     type Item = T;
//     
//     fn next(&mut self) -> Option<T> {
//         match self.it.next() {
//             None => None,
//             Some(x) => {
//                self.save.push(x.clone());
//                Some(x)
//             }
//         }
//     }
// }


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union() {
        assert_eq!(
            union(VecDeque::from(vec!['a', 'b', 'c', 'a']), VecDeque::from(vec!['b', 'x', 'y', 'x'])),
            VecDeque::from(vec!['a', 'b', 'c', 'a', 'x', 'y']))
    }
}

