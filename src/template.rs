#![allow(dead_code)]

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

    pub fn replace(&mut self, key: &str, replacement: &str)  {
        for i in 0..self.0.len() {
            match &self.0[i] {
                TemplateBit::Key(indent, s) => if s == key {
                    self.0[i] = TemplateBit::Raw(util::indent(*indent, replacement));
                }
                _ => (),
            }
        }
    }

    pub fn to_string(self) -> Result<String, String> {
        let mut result = String::new();
        for x in self.0 {
            match x {
                TemplateBit::Raw(s) => {
                   result.push_str(&s);
                   ()
                }
                TemplateBit::Key(_, k) =>
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
    Key(usize, String), //the first member usize represents the indentation
}

impl TemplateBit {
    pub fn raw(s: &str) -> TemplateBit {
        TemplateBit::Raw(s.to_string())
    }

    pub fn key(indent: usize, s: &str) -> TemplateBit {
        TemplateBit::Key(indent, s.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_template_to_string() {
        
        let mut template = Template(vec![TemplateBit::key(0, "x")]);
        template.replace("x", "Bla");
        assert_eq!(template.to_string(),
            Ok(String::from("Bla")));

        let mut template = Template(vec![TemplateBit::key(1, "x")]);
        template.replace("x", "Bla\nBla");
        assert_eq!(template.to_string(),
            Ok(String::from(" Bla\n Bla")));

        let mut template = Template(vec![
            TemplateBit::raw("A "), TemplateBit::key(0, "x"), TemplateBit::raw("\n"),
            TemplateBit::key(1, "y"), TemplateBit::raw("\n"),
            TemplateBit::key(0, "x")]);
        template.replace("x", "Bla");
        template.replace("y", "Greu");
        assert_eq!(template.to_string(),
            Ok(String::from("A Bla\n Greu\nBla")));
    }

}
