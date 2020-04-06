#![allow(dead_code)]

use crate::type_sy::{Type};
use crate::type_sy::{t_var_0, t_fun_seq, t_con, t_pair, t_list_t, t_int, t_double, t_param};

pub fn a() -> Type {t_var_0("a")}
pub fn b() -> Type {t_var_0("b")}
pub fn c() -> Type {t_var_0("c")}
pub fn x() -> Type {t_var_0("x")}
pub fn y() -> Type {t_var_0("y")}

pub fn cons() -> Vec<(String, Type)> {
    vec![
        // calibrate: PosteriorDistribution -> SCRIPT
        (String::from("calibrate"),
            t_fun_seq(&[t_param("PosteriorDistribution", &[x(), y()]), t_con("SCRIPT")])),
        // manual_input: ManualInput
        (String::from("manual_input"),
            t_con("ManualInput")),
        // manual_var_name: ManualInput -> VarName
        (String::from("manual_var_name"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("VarName")])),
        // manual_int: ManualInput -> Int
        (String::from("manual_int"), 
            t_fun_seq(&[t_con("ManualInput"), t_int()])),
        // manual_double: ManualInput -> Double
        (String::from("manual_double"),
            t_fun_seq(&[t_con("ManualInput"), t_double()])),
        // manual_address: ManualInput -> Address
        (String::from("manual_address"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("Address")])),
        // manual_login: ManualInput -> Login
        (String::from("manual_login"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("Login")])),
        // manual_vo: ManualInput -> VO
        (String::from("manual_vo"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("VO")])),
        // manual_cpu_time: ManualInput -> CpuTime
        (String::from("manual_cpu_time"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("CpuTime")])),
        // manual_openmole_memory: ManualInput -> OpenMoleMemory
        (String::from("manual_openmole_memory"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("OpenMoleMemory")])),
        // var_int: VarName -> Var Int
        (String::from("var_int"), 
            t_fun_seq(&[t_con("VarName"), t_param("Var", &[t_int()])])),
        // var_double: VarName -> Var Double
        (String::from("var_double"), 
            t_fun_seq(&[t_con("VarName"), t_param("Var", &[t_double()])])),
        // add_element: a -> [a] -> [a]
        (String::from("add_element"), 
            t_fun_seq(&[a(), t_list_t(a()), t_list_t(a())])),
        // no_more_elements: [a]
        (String::from("no_more_elements"), 
            t_fun_seq(&[t_list_t(a())])),
        // single_input: Var x -> Inputs x
        (String::from("single_input"), 
            t_fun_seq(&[t_param("Var", &[x()]), t_param("Inputs", &[x()])])),
        // add_input: Var a -> Inputs b -> Inputs (a, b)
        (String::from("add_input"), 
            t_fun_seq(&[t_param("Var", &[a()]), t_param("Inputs", &[b()]), t_param("Inputs", &[t_pair(a(), b())])])),
        // no_more_inputs: Inputs b
        (String::from("no_more_inputs"), 
            t_fun_seq(&[t_param("Inputs", &[b()])])),
        // list_inputs: [Var a] -> Inputs [a]
        (String::from("list_inputs"), 
            t_fun_seq(&[t_list_t(t_param("Var", &[a()])), t_param("Inputs", &[a()])])),
        // single_output: Var x -> Outputs x
        (String::from("single_output"), 
            t_fun_seq(&[t_param("Var", &[x()]), t_param("Outputs", &[x()])])),
        // add_output: Var a -> Outputs b -> Outputs (a, b)
        (String::from("add_output"), 
            t_fun_seq(&[t_param("Var", &[a()]), t_param("Outputs", &[b()]), t_param("Outputs", &[t_pair(a(), b())])])),
        // no_more_outputs: Inputs b
        (String::from("no_more_outputs"), 
            t_fun_seq(&[t_param("Inputs", &[b()])])),
        // list_outputs: [Var a] -> Outputs [a]
        (String::from("list_outputs"), 
            t_fun_seq(&[t_list_t(t_param("Var", &[a()])), t_param("Outputs", &[t_list_t(a())])])),
        // scala_model: ScalaCode -> Inputs x -> Outputs y -> t_param("Model", &[x(), y()])
        (String::from("scala_model"), 
            t_fun_seq(&[t_con("ScalaCode"), t_param("Inputs", &[x()]), t_param("Outputs", &[y()]), t_param("Model", &[x(), y()])])),
        // netlogo_6_model: NetLogoCode -> NetLogoSetup -> Inputs x -> Outputs y -> Model x y
        (String::from("netlogo_6_model"), 
            t_fun_seq(&[t_con("NetLogoCode"), t_con("NetLogoSetup"), t_param("Inputs", &[x()]), t_param("Outputs", &[y()]), t_param("Model", &[x(), y()])])),
        // r_model: RCode -> Inputs x -> Outputs y -> Model x y
        (String::from("r_model"), 
            t_fun_seq(&[t_con("RCode"), t_param("Inputs", &[x()]), t_param("Outputs", &[y()]), t_param("Model", &[x(), y()])])),
        // replicate: Int -> Model x y -> Model x [y]
        (String::from("replicate"), 
            t_fun_seq(&[t_int(), t_param("Model", &[x(), y()]), t_param("Model", &[x(), t_list_t(y())])])),
        // direct_sampling: Sample x -> Model x y -> Model x [y]
        (String::from("direct_sampling"), 
            t_fun_seq(&[t_param("Sample", &[x()]), t_param("Model", &[x(), y()]), t_param("Model", &[x(), t_list_t(y())])])),
        // scala_code_from_file: FilePath -> ScalaCode
        (String::from("scala_code_from_file"), 
            t_fun_seq(&[t_con("FilePath"), t_con("ScalaCode")])),
        // manual_scala_code: ManualInput -> ScalaCode
        (String::from("manual_scala_code"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("ScalaCode")])),
        // netlogo_code_from_file: FilePath -> NetLogoCode
        (String::from("netlogo_code_from_file"), 
            t_fun_seq(&[t_con("FilePath"), t_con("NetLogoCode")])),
        // netlogo_setup_from_file: FilePath -> NetLogoSetup
        (String::from("netlogo_setup_from_file"), 
            t_fun_seq(&[t_con("FilePath"), t_con("NetLogoSetup")])),
        // manual_netlogo_setup: ManualInput -> ManualInput -> ManualInput -> NetLogoSetup
        (String::from("manual_netlogo_setup"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("ManualInput"), t_con("ManualInput"), t_con("NetLogoSetup")])),
        // r_code_from_file: FilePath -> RCode
        (String::from("r_code_from_file"), 
            t_fun_seq(&[t_con("FilePath"), t_con("RCode")])),
        // manual_input_r_code: ManualInput -> RCode
        (String::from("manual_input_r_code"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("RCode")])),
        // lhs: SampleSize -> Bounds x -> Sample x
        (String::from("lhs"), 
            t_fun_seq(&[t_con("SampleSize"), t_param("Bounds", &[x()]), t_param("Sample", &[x()])])),
        // sobol: SampleSize -> Bounds x -> Sample x
        (String::from("sobol"), 
            t_fun_seq(&[t_con("SampleSize"), t_param("Bounds", &[x()]), t_param("Sample", &[x()])])),
        // uniform: SampleSize -> Double -> Sample Double
        (String::from("uniform"), 
            t_fun_seq(&[t_con("SampleSize"), t_double(), t_param("Sample", &[t_double()])])),
        // csv_sampling: MappedInput x -> CSVSeparator -> Sample x
        (String::from("csv_sampling"), 
            t_fun_seq(&[t_param("MappedInput", &[x()]), t_con("CSVSeparator"), t_param("Sample", &[x()])])),
        // full_factorial: Sample a -> Sample b -> Sample (a,b)
        (String::from("full_factorial"), 
            t_fun_seq(&[t_param("Sample", &[a()]), t_param("Sample", &[b()]), t_param("Sample",  &[t_pair(a(),b())])])),
        // concat_sampling: Sample a -> Sample a -> Sample a
        (String::from("concat_sampling"), 
            t_fun_seq(&[t_param("Sample", &[a()]), t_param("Sample", &[a()]), t_param("Sample", &[a()])])),
        // zip_sampling: Sample a -> Sample b -> Sample (a,b)
        (String::from("zip_sampling"), 
            t_fun_seq(&[t_param("Sample", &[a()]), t_param("Sample", &[b()]), t_param("Sample",  &[t_pair(a(),b())])])),
        // resample: Int -> Sample a -> Sample [a]
        (String::from("resample"), 
            t_fun_seq(&[t_int(), t_param("Sample", &[a()]), t_param("Sample", &[t_list_t(a())])])),
        // calibrate: Termination -> PopulationSize -> Bounds x -> DataPoint y -> Model x y -> Pareto x
        (String::from("calibrate"), 
            t_fun_seq(&[t_con("Termination"), t_con("PopulationSize"), t_param("Bounds", &[x()]), t_param("DataPoint", &[y()]), t_param("Model", &[x(), y()]), t_param("Pareto", &[x()])])),
        // morris: Input x -> Output x -> Bounds x -> MorrisRepetitions -> MorrisLevels -> Model x y -> MorrisSensitivityIndex x y
        (String::from("morris"), 
            t_fun_seq(&[t_param("Input", &[x()]), t_param("Output", &[x()]), t_param("Bounds", &[x()]), t_con("MorrisRepetitions"), t_con("MorrisLevels"), t_param("Model", &[x(), y()]), t_param("MorrisSensitivityIndex", &[x(), y()])])),
        // saltelli: Input x -> Output x -> Bounds x -> SampleSize  -> Model x y -> GlobalSensitivityIndex x y
        (String::from("saltelli"), 
            t_fun_seq(&[t_param("Input", &[x()]), t_param("Output", &[x()]), t_param("Bounds", &[x()]), t_con("SampleSize"), t_param("Model", &[x(), y()]), t_param("GlobalSensitivityIndex", &[x(), y()])])),
        // profile: Termination -> SubIntervalSize -> GetParam x xi -> Bounds x -> DataPoint y -> Model x y -> Profile xi
        (String::from("profile"), 
            t_fun_seq(&[t_con("Termination"), t_con("SubIntervalSize"), t_param("GetParam", &[x(), t_var_0("xi")]), t_param("Bounds", &[x()]), t_param("DataPoint", &[y()]), t_param("Model", &[x(), y()]), t_param("Profile", &[t_var_0("xi")])])),
        // pse: Termination -> Bounds x -> Grid y -> Model x y -> Diversity y
        (String::from("pse"), 
            t_fun_seq(&[t_con("Termination"), t_param("Bounds", &[x()]), t_param("Grid", &[y()]), t_param("Model", &[x(), y()]), t_param("Diversity", &[y()])])),
        // abc: ABCTermination -> SampleSize -> PriorDistribution x -> DataPoint y -> Model x y -> PosteriorDistribution x y
        (String::from("abc"), 
            t_fun_seq(&[t_con("ABCTermination"), t_con("SampleSize"), t_param("PriorDistribution", &[x()]), t_param("DataPoint", &[y()]), t_param("Model", &[x(), y()]), t_param("PosteriorDistribution", &[x(), y()])])),
        // abc_termination: ABCTermination
        (String::from("abc_termination"),
            t_con("ABCTermination")),
        // local: Int -> Environment
        (String::from("local"), 
            t_fun_seq(&[t_int(), t_con("Environment")])),
        // ssh: Address -> Login -> Int -> Environment
        (String::from("ssh"), 
            t_fun_seq(&[t_con("Address"), t_con("Login"), t_int(), t_con("Environment")])),
        // pbs: Address -> Login -> Environment
        (String::from("pbs"), 
            t_fun_seq(&[t_con("Address"), t_con("Login"), t_con("Environment")])),
        // egi: VO -> CpuTime -> OpenMoleMemory -> Environment
        (String::from("egi"), 
            t_fun_seq(&[t_con("VO"), t_con("CpuTime"), t_con("OpenMoleMemory"), t_con("Environment")])),
    ]
}
