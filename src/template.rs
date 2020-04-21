#![allow(dead_code)]

use std::collections::HashSet;

use crate::util;

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
pub struct Template(pub Vec<TemplateBit>);

impl Template {
    // pub fn new(keys: Vec<(usize, &str)>, body: &str) -> Template {
    //     let mut sequence : Vec<TemplateBit> = Vec::new();
    //     let mark : usize = 0;
    //     for (ind, k) in keys {
    //         for (i, _) in body.match_indices(&format!("{{{}}}", k)) {
    //             if mark - (i - ind) > 0 {
    //                 sequence.push(TemplateBit::Raw(body[mark..i - ind].to_string()));
    //             }
    //             sequence.push(TemplateBit::Key(ind, k.clone()));
    //             mark = i;
    //         }
    //     }

    //     if mark < body.len() {
    //         sequence.push(TemplateBit::Raw(body[mark..].to_string()));
    //     }

    //     Template(sequence)
    // }

    pub fn keys<'a>(&'a self) -> HashSet<&'a String>{
        let get_key = |b: &'a TemplateBit| -> Option<&'a String> {
            match b {
                TemplateBit::Key(s) => Some(&s),
                _ => None,
            }
        };

        self.0.iter().filter_map(get_key).collect()
    }

    pub fn replace(&mut self, key: &str, replacement: &str)  {
        for i in 0..self.0.len() {
            match &self.0[i] {
                TemplateBit::Key(s) => if s == key {
                    self.0[i] = TemplateBit::Raw(replacement.to_string());
                }
                _ => (),
            }
        }
    }

    pub fn to_string(self) -> Result<String, String> {
        let mut current_indent = 0;
        let mut line_start = true;
        let mut result = String::new();
        for x in self.0 {
            match x {
                TemplateBit::Indent(indent) => {
                    if !result.is_empty() {
                        result.push_str("\n");
                    }
                    current_indent = indent;
                    line_start = true;
                    ()
                }
                TemplateBit::Raw(s) => {
                    if line_start {
                       result.push_str(&util::indent(current_indent, &s, false));
                       line_start = false;
                    } else {
                       result.push_str(&util::indent(current_indent, &s, true));
                    }
                    ()
                },
                TemplateBit::Key(k) =>
                   return Err(format!("Template::to_string: keys remaining: {}", k)),
            }
        }

        Ok(result)
    }
}

// // Compute the indentation in body at the given position.
// fn compute_indentation(body: &str, mut pos: usize) -> usize {
// 
//     let res = 0;
// 
//     pos -= 1;
// 
//     while pos >= 0 && body[pos].is_whitespace() && body[pos] != '\n' {
//         res += 1;
//         pos -= 1;
//     }
// 
//     res
// }

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
#[derive(Eq)]
pub enum TemplateBit {
    Raw(String),
    Key(String),
    Indent(usize),
}

impl TemplateBit {
    pub fn raw(s: &str) -> TemplateBit {
        TemplateBit::Raw(s.to_string())
    }

    pub fn key(s: &str) -> TemplateBit {
        TemplateBit::Key(s.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_template_to_string() {
        
        let mut template = Template(vec![TemplateBit::Indent(0), TemplateBit::key("x")]);
        template.replace("x", "Bla");
        assert_eq!(template.to_string(),
            Ok(String::from("Bla")));

        let mut template = Template(vec![TemplateBit::Indent(1), TemplateBit::key("x")]);
        template.replace("x", "Bla\nBla");
        assert_eq!(template.to_string(),
            Ok(String::from(" Bla\n Bla")));

        let mut template = Template(vec![
            TemplateBit::Indent(0), TemplateBit::raw("A "), TemplateBit::key("x"),
            TemplateBit::Indent(1), TemplateBit::key("y"),
            TemplateBit::Indent(0), TemplateBit::key("x")]);
        template.replace("x", "Bla");
        template.replace("y", "Greu");
        assert_eq!(template.to_string(),
            Ok(String::from("A Bla\n Greu\nBla")));
    }

}
