mod cat;
mod parse;
mod template;
mod cons;
mod util;
mod type_sy;

use std::fs;
use std::collections::HashSet;
use std::io;
use std::io::Write;
use std::iter::Iterator;
use std::vec;
use structopt::StructOpt;

//use parse::*;

use type_sy::{Type};
use type_sy::{t_fun, t_con, t_var_0};
use template::Template;

use cat::{
    morph_schemes_from_cons, MorphScheme, Morphism, morphisms_bf, morphisms_from_source,
};

use cons::{Cons, Cons::Id, uncat_cons, pair, list_no_cons, run_special_cons};

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
    Interact,
}

impl Default for OutputType {
    fn default() -> Self { OutputType::Info }
}

fn main() {
    let args = Cli::from_args();
    let predef_cons = cons::predef_cons();
    let input_cons = match cons_from_file("openmole.cons") {
        Err(parse_err) => {
            eprintln!("Could not parse constructor input file.");
            eprintln!("Parse Error: {}", parse_err);
            panic!();
        }
        Ok(x) => x,
    };
    let all_cons_sig: Vec<(String, Cons, Type, Vec<String>)> =
        input_cons.iter().map(|(nam,cons,typ,args,_)|
             (nam.clone(), cons.clone(), typ.clone(), args.clone()))
        .chain(predef_cons.iter().map(|(nam,cons,typ,args)|
             (nam.clone(), cons.clone(), typ.clone(), args.clone())))
        .collect();
    let script = |c: &Cons| -> Result<String, String> { cons::script_template( c, &input_cons ) };

    // Types that have no constructors:
    let no_cons = list_no_cons(&all_cons_sig);
    if !no_cons.is_empty() {
        eprintln!("The following types have no constructors:");
        for (n, t) in no_cons {
            eprintln!("    {} from constructor {}", t, n);
        }
    } else {
        let cons = cons::cat_cons(all_cons_sig.clone());
        let morph_schemes = morph_schemes_from_cons(&cons);
        match args.output_type {
           Some(OutputType::Info) => output_info(&input_cons, &morph_schemes),
           Some(OutputType::GraphViz) => output_gv(&morph_schemes),
           None | Some(OutputType::Interact) => interact(&morph_schemes, script),
        }
    }
}


fn cons_from_file(filename: &str) -> Result<Vec<(String, Cons, Type, Vec<String>, Template)>, parse::ParseError> {

    let input_stream = fs::read_to_string(filename)
        .expect(&format!("Could not read file {}", filename));

    let cons = parse::parse_constructors(
        &mut parse::State::new(input_stream.chars()))?;

    let res = (0..).zip(cons.into_iter())
        .map(|(i, (name, typ, args, body))| (name, Cons::Data(i), typ, args, body))
        .collect();

    Ok(res)
}

fn start_type() -> Type {
    t_fun(t_con("SCRIPT"), t_con("SCRIPT"))
}

fn output_info(cons: &Vec<(String, Cons, Type, Vec<String>, Template)>, morph_schemes: &Vec<MorphScheme>) {
    println!("User defined Constructors");
    for (name, c, t, _, _) in cons.iter() {
      println!("    {}. {} : {}", c, name, t);
    }
    println!("");

    println!("Morph Schemes:");
    for m in morph_schemes.iter() {
      println!("    {}", m);
    }
    println!("");

    let start = start_type();
    println!("Start type:");
    println!("    {}", start);
}


fn output_gv(morph_schemes: &Vec<MorphScheme>) {
    let start = start_type();

    let edges =
        morphisms_bf(&vec![&start], &morph_schemes);

    fn format_dot_edge(m: &Morphism) -> String {
        // "((-> Domain) Domain)" -> "Domain" [ label = "&unit_domain" ]
        format!("\"{src}\" -> \"{tgt}\" [ label=\"{name}\" ]",
                src = m.source,
                tgt = m.target,
                name = m.name)
    }

    let mut edges_set : HashSet<Morphism> = HashSet::new();

    println!("digraph {{");
    println!("    node [ shape=point ] ");
    println!("    \"(SCRIPT -> SCRIPT)\" [ shape=ellipse label=START]");
    println!("    \"SCRIPT\" [ shape=ellipse label=END]");
    for p in edges {
        let is_new = edges_set.insert(p.clone());
        if is_new {
            println!("    {}", format_dot_edge(&p));
        }
    }
    println!("}}");
}

fn interact<F>(morph_schemes: &Vec<MorphScheme>, script: F)
where F: Fn(&Cons) -> Result<String, String>,
{
    let stop_type = t_con("SCRIPT");
    let mut cur_type = start_type();
    let mut cur_morphism = Morphism::new("id", Id, t_var_0("a"), t_var_0("a"), vec!["The script is".to_string()]);
    let mut input = String::new();

    while cur_type != stop_type {
        println!("");

        match cur_morphism.target.fun_source() {
            None =>
                println!("What kind of simulation experiment to you want to perform?"),
            Some(_) => {
                println!("{}.\nWe need to construct a value for the latter argument. Please choose a constructor:",
                    cur_morphism.cons_arg_names.first().unwrap_or(&"???".to_string()));
            }
        };

        let candidates = morphisms_from_source(&cur_type, morph_schemes);

        let mut selected_morphism: Morphism =
            if candidates.len() < 1 {
                panic!("No candidate morphism.");
            } else if candidates.len() == 1 {
                let s = candidates.first().unwrap().clone();
                println!("There is only one constructor compatible: \x1B[33;1m{}\x1B[0m", s.name);
                print!("Selecting it automatically. Press Enter to continue...");
                io::stdout().flush().unwrap();
                io::stdin().read_line(&mut input).ok();
                s
            } else {
                for (i, m) in (0..).zip(candidates.iter()) {
                   println!("    {}: \x1B[33;1m{}\x1B[0m", i, m.name);
                }

                loop {
                    print!("Select [0]> ");
                    io::stdout().flush().unwrap();
                    input.clear();
                    match io::stdin().read_line(&mut input) {
                        Err(e) => {
                            println!("Failed to read input: {}", e);
                            continue
                        }
                        Ok(_) => (),
                    }

                    let trimmed = input.trim();

                    if trimmed.is_empty() {
                        break candidates.first().unwrap().clone()
                    } else {
                        match trimmed.parse::<usize>() {
                            Err(e) => {
                                println!("Failed to parse input: {}", e);
                                continue
                            }
                            Ok(s) => break candidates.get(s).unwrap().clone(),
                        }
                    }
                }
            };

        selected_morphism.cons = run_special_cons(&selected_morphism.cons);

        cur_morphism = cur_morphism.and_then(&selected_morphism)
            .expect("Failed to chain new morphism.");
        cur_type = cur_morphism.target.clone();
    }
    println!("");

    println!("Final morphism: {}", cur_morphism);

    println!("---- Script ----");

    let the_script = pair(cur_morphism.cons, Id);
    println!("{}", script(&uncat_cons(&the_script)).expect("SCRIPT NOT OK."));
}

