use std::collections::VecDeque;
use std::fmt::Display;
use std::iter;

pub fn indent(width: usize, txt: &str, skip_first_line: bool) -> String {
    let indent: String = iter::repeat(" ").take(width).collect();
    let mut lines = txt.lines();

    // First line.
    let mut result: String = String::new();

    match lines.next() {
        None => (),
        Some(l) => {
            if !skip_first_line {
                result.push_str(&indent);
            }
            result.push_str(l);
        }
    }

    for l in lines {
        result.push_str("\n");
        result.push_str(&indent);
        result.push_str(l);
    }

    result
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union() {
        assert_eq!(
            union(VecDeque::from(vec!['a', 'b', 'c', 'a']), VecDeque::from(vec!['b', 'x', 'y', 'x'])),
            VecDeque::from(vec!['a', 'b', 'c', 'a', 'x', 'y']))
    }
    
    #[test]
    fn test_indent() {
        assert_eq!(indent(2, "a\n b", false), "  a\n   b".to_string());
        assert_eq!(indent(2, "a\n b", true), "a\n   b".to_string());
    }
}

