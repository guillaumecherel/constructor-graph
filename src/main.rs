mod cat;
mod cons;
mod util;
mod type_sy;

use std::collections::HashSet;
use std::io;
use std::iter::Iterator;
use std::vec;
use structopt::StructOpt;

use type_sy::{Type};
use type_sy::{t_fun, t_con, t_var_0};

use cat::{
    morph_schemes_from_cons, MorphScheme, Morphism, morphisms_bf, morphisms_from_source,
};

use cons::{Cons, Cons::Id, uncat_cons, pair};

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
    let input_cons = cons::test_cons_2();
    let script = |c: &Cons| -> String { cons::script_cons(c, &input_cons) };
    let cons = cons::cat_cons(input_cons.clone());
    let morph_schemes = morph_schemes_from_cons(&cons);
    match args.output_type {
       None => output_info(&input_cons, &morph_schemes),
       Some(OutputType::Info) => output_info(&input_cons, &morph_schemes),
       Some(OutputType::GraphViz) => output_gv(&morph_schemes),
       Some(OutputType::Interact) => interact(&morph_schemes, script),
    }
}


// fn terms_from_file(filename: String) -> Vec<Cons> {
// 
//     let input_stream = fs::read_to_string(filename).unwrap();
// 
//     let cons = parse_terms(input_stream.into_iter()).unwrap();
// 
//     let morph_schemes = morph_schemes_from_cons(&cons);
// 
//     (cons, morph_schemes)
// }

fn start_type() -> Type {
    t_fun(t_con("SCRIPT"), t_con("SCRIPT"))
}

fn output_info(cons: &Vec<(String, Type)>, morph_schemes: &Vec<MorphScheme>) {
    println!("User defined Constructors");
    for (i, (name, t)) in (0..).zip(cons.iter()) {
      println!("    {}. {} : {}", i, name, t);
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

    let edges_set: HashSet<Morphism> =
        morphisms_bf(&vec![&start], &morph_schemes).take(1000).collect();
    println!("# !!! WARNING REMOVE TAKE !!!");

    fn format_dot_edge(m: &Morphism) -> String {
        // "((-> Domain) Domain)" -> "Domain" [ label = "&unit_domain" ]
        format!("\"{src}\" -> \"{tgt}\" [ label=\"{name}\" ]",
                src = m.source,
                tgt = m.target,
                name = m.name)
    }

    println!("digraph {{");
    //println!("    node [ shape=point ] ");
    //println!("    \"(SCRIPT -> a)\" [ shape=ellipse ]");
    //println!("    \"SCRIPT\" [ shape=ellipse ]");
    for m in edges_set {
        println!("    {}", format_dot_edge(&m));
    }
    println!("}}");
}

fn interact<F>(morph_schemes: &Vec<MorphScheme>, script: F)
where F: Fn(&Cons) -> String,
{
    let stop_type = t_con("SCRIPT");
    let mut cur_type = start_type();
    let mut cur_morphism = Morphism::new("id", Id, t_var_0("a"), t_var_0("a"));
    let mut input = String::new();
    let mut selection: usize;

    while cur_type != stop_type {
        println!("");
        println!("Current morphism: {}", cur_morphism);
        println!("Chain with:");

        let candidates = morphisms_from_source(&cur_type, morph_schemes);

        for (i, m) in (0..).zip(candidates.iter()) {
           println!("{}: {}", i, m);
        }

        input.clear();
        io::stdin().read_line(&mut input).expect("Failed to read line");
        println!("input {}", input);
        selection = input.trim().parse::<usize>().expect("Failed to parse input");

        cur_morphism = cur_morphism.and_then(&candidates[selection])
            .expect("Failed to chain new morphism.");
        cur_type = cur_morphism.target.clone();
    }
    println!("");

    println!("Final morphism: {}", cur_morphism);

    println!("---- Script ----");

    let the_script = pair(cur_morphism.cons, Id);
    println!("{}", script(&uncat_cons(&the_script)));
}

