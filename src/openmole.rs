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
        (String::from("calibrate"),
            t_fun_seq(&[t_param("PosteriorDistribution", &[x(), y()]), t_con("SCRIPT")])),
        (String::from("profile"),
            t_fun_seq(&[t_con("Profile"), t_con("SCRIPT")])),
        (String::from("diversity"),
            t_fun_seq(&[t_param("Diversity", &[t_double()]), t_con("SCRIPT")])),
        (String::from("sample_model_output"),
            t_fun_seq(&[t_param("SimulationRuns", &[x(), y()]), t_con("SCRIPT")])),

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
        // manual_file_path: ManualInput -> FilePath
        (String::from("manual_file_path"),
            t_fun_seq(&[t_con("ManualInput"), t_con("FilePath")])),
        // manual_address: ManualInput -> Address
        (String::from("manual_address"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("Address")])),
        // manual_login: ManualInput -> Login
        (String::from("manual_login"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("Login")])),
        // manual_csv_separator: ManualInput -> CsvSeparator
        (String::from("manual_csv_separator"),
            t_fun_seq(&[t_con("ManualInput"), t_con("CsvSeparator")])),
        // manual_vo: ManualInput -> VO
        (String::from("manual_vo"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("VO")])),
        // manual_cpu_time: ManualInput -> CpuTime
        (String::from("manual_cpu_time"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("CpuTime")])),
        // manual_openmole_memory: ManualInput -> OpenMoleMemory
        (String::from("manual_openmole_memory"), 
            t_fun_seq(&[t_con("ManualInput"), t_con("OpenMoleMemory")])),
        // data_point: y -> DataPoint y
        (String::from("manual_data_point"),
            t_fun_seq(&[t_con("ManualInput"), t_param("DataPoint", &[y()])])),
        // population_size: Int -> PopulationSize
        (String::from("population_size"),
            t_fun_seq(&[t_int(), t_con("PopulationSize")])),
        // bounds: [(x, x)] -> Bounds x
        (String::from("bounds"),
            t_fun_seq(&[t_list_t(t_pair(x(), x())), t_param("Bounds", &[x()])])),

        // var_int: VarName -> Var Int
        (String::from("var_int"), 
            t_fun_seq(&[t_con("VarName"), t_param("Var", &[t_int()])])),
        // var_double: VarName -> Var Double
        (String::from("var_double"), 
            t_fun_seq(&[t_con("VarName"), t_param("Var", &[t_double()])])),

        // pair: a -> b -> (a, b)
        (String::from("pair"),
            t_fun_seq(&[a(), b(), t_pair(a(), b())])),

        // add_element: a -> [a] -> [a]
        (String::from("add_element"), 
            t_fun_seq(&[a(), t_list_t(a()), t_list_t(a())])),
        // no_more_elements: [a]
        (String::from("no_more_elements"), 
            t_fun_seq(&[t_list_t(a())])),

        // add_input: Var a -> Input b -> Input (a, b)
        (String::from("add_input"), 
            t_fun_seq(&[t_param("Var", &[a()]), t_param("Input", &[b()]), t_param("Input", &[t_pair(a(), b())])])),
        // no_more_inputs: Input b
        (String::from("no_more_inputs"), 
            t_fun_seq(&[t_param("Input", &[b()])])),
        // list_inputs: [Var a] -> Input [a]
        (String::from("list_inputs"), 
            t_fun_seq(&[t_list_t(t_param("Var", &[a()])), t_param("Input", &[t_list_t(a())])])),

        // mapped_input: Var x -> VarName -> MappedInput x
        (String::from("mapped_input"),
            t_fun_seq(&[t_param("Var", &[x()]), t_con("VarName"), t_param("MappedInput", &[x()])])),
        // add_mapped_input: Var a -> VarName -> MappedInput b -> MappedInput (a,b)
        (String::from("add_mapped_input"),
            t_fun_seq(&[t_param("Var", &[a()]), t_con("VarName"), t_param("MappedInput", &[a()])])),
        // no_more_mapped_input: MappedInput a
        (String::from("no_more_mapped_input"),
            t_param("MappedInput", &[a()])),

        // add_output: Var a -> Output b -> Output (a, b)
        (String::from("add_output"), 
            t_fun_seq(&[t_param("Var", &[a()]), t_param("Output", &[b()]), t_param("Output", &[t_pair(a(), b())])])),
        // no_more_outputs: Output b
        (String::from("no_more_outputs"), 
            t_fun_seq(&[t_param("Output", &[b()])])),
        // list_outputs: [Var a] -> Output [a]
        (String::from("list_outputs"), 
            t_fun_seq(&[t_list_t(t_param("Var", &[a()])), t_param("Output", &[t_list_t(a())])])),

        // scala_model: ScalaCode -> Input x -> Output y -> t_param("Model", &[x(), y()])
        (String::from("scala_model"), 
            t_fun_seq(&[t_con("ScalaCode"), t_param("Input", &[x()]), t_param("Output", &[y()]), t_param("Model", &[x(), y()])])),
        // netlogo_6_model: NetLogoCode -> NetLogoSetup -> Input x -> Output y -> Model x y
        (String::from("netlogo_6_model"), 
            t_fun_seq(&[t_con("NetLogoCode"), t_con("NetLogoSetup"), t_param("Input", &[x()]), t_param("Output", &[y()]), t_param("Model", &[x(), y()])])),
        // r_model: RCode -> Input x -> Output y -> Model x y
        (String::from("r_model"), 
            t_fun_seq(&[t_con("RCode"), t_param("Input", &[x()]), t_param("Output", &[y()]), t_param("Model", &[x(), y()])])),
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
        // csv_sampling: MappedInput x -> CsvSeparator -> Sample x
        (String::from("csv_sampling"), 
            t_fun_seq(&[t_param("MappedInput", &[x()]), t_con("CsvSeparator"), t_param("Sample", &[x()])])),
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

        // run_simulations: Sample x -> Model x y -> SimulationRuns x y
        (String::from("run_simulations"),
            t_fun_seq(&[t_param("Sample", &[x()]), t_param("Model", &[x(), y()]), t_param("SimulationRuns", &[x(), y()])])),
        // calibrate: Termination -> PopulationSize -> Bounds x -> DataPoint y -> Model x y -> Pareto x
        (String::from("calibrate"), 
            t_fun_seq(&[t_con("Termination"), t_con("PopulationSize"), t_param("Bounds", &[x()]), t_param("DataPoint", &[y()]), t_param("Model", &[x(), y()]), t_param("Pareto", &[x()])])),
        // morris: Input x -> Output x -> Bounds x -> MorrisRepetitions -> MorrisLevels -> Model x y -> MorrisSensitivityIndex x y
        (String::from("morris"), 
            t_fun_seq(&[t_param("Input", &[x()]), t_param("Output", &[x()]), t_param("Bounds", &[x()]), t_con("MorrisRepetitions"), t_con("MorrisLevels"), t_param("Model", &[x(), y()]), t_param("MorrisSensitivityIndex", &[x(), y()])])),
        // morris_repetitions: Int -> MorrisRepetitions
        (String::from("morris_repetitions"),
            t_fun_seq(&[t_int(), t_con("MorrisRepetitions")])),
        // morris_levels: Int -> MorrisLevels
        (String::from("morris_levels"),
            t_fun_seq(&[t_int(), t_con("MorrisLevels")])),
        // saltelli: Input x -> Output x -> Bounds x -> SampleSize  -> Model x y -> GlobalSensitivityIndex x y
        (String::from("saltelli"), 
            t_fun_seq(&[t_param("Input", &[x()]), t_param("Output", &[x()]), t_param("Bounds", &[x()]), t_con("SampleSize"), t_param("Model", &[x(), y()]), t_param("GlobalSensitivityIndex", &[x(), y()])])),
        // profile: Termination -> SubIntervalSize -> Input Double -> Bounds [Double] -> DataPoint [Double] -> Model [Double] [Double] -> Profile
        (String::from("profile"), 
            t_fun_seq(&[t_con("Termination"), t_con("SubIntervalSize"), t_param("Input", &[t_list_t(t_double())]), t_param("Bounds", &[t_double()]), t_param("DataPoint", &[t_double()]), t_param("Model", &[t_double(), t_double()]), t_con("Profile")])),
        // sub_interval_size: Int -> SubIntervalSize
        (String::from("sub_interval_size"),
            t_fun_seq(&[t_double(), t_con("SubIntervalSize")])),
        // pse: Termination -> Bounds x -> Grid y -> Model x y -> Diversity y
        (String::from("pse"), 
            t_fun_seq(&[t_con("Termination"), t_param("Bounds", &[t_double()]), t_param("Grid", &[t_double()]), t_param("Model", &[t_list_t(t_double()), t_list_t(t_double())]), t_param("Diversity", &[t_double()])])),
        // grid: [Double] -> Grid Double
        (String::from("grid"),
            t_fun_seq(&[t_list_t(t_double()), t_param("Grid", &[t_double()])])),
        // max_simu_termination: Int -> Termination
        (String::from("max_simu_termination"),
            t_fun_seq(&[t_int(), t_con("Termination")])),
        // max_seconds_termination: Int -> Termination
        (String::from("max_seconds_termination"),
            t_fun_seq(&[t_int(), t_con("Termination")])),
        // max_hours_termination: Int -> Termination
        (String::from("max_hours_termination"),
            t_fun_seq(&[t_int(), t_con("Termination")])),
        // abc: Termination -> SampleSize -> PriorDistribution x -> DataPoint y -> Model x y -> PosteriorDistribution x y
        (String::from("abc"), 
            t_fun_seq(&[t_con("Termination"), t_con("SampleSize"), t_param("Distribution", &[x()]), t_param("DataPoint", &[y()]), t_param("Model", &[x(), y()]), t_param("PosteriorDistribution", &[x(), y()])])),
        // sample_size: Int -> SampleSize
        (String::from("sample_size"),
            t_fun_seq(&[t_int(), t_con("SampleSize")])),
        // uniform_distribution: [(Double, Double)] -> Distribution [Double]
        (String::from("uniform_distribution"),
            t_fun_seq(&[t_list_t(t_pair(t_double(), t_double())), t_param("Distribution", &[t_double()])])),
        // beta_distribution: [(Double, Double)] -> Distribution [Double]
        (String::from("beta_distribution"),
            t_fun_seq(&[t_list_t(t_pair(t_double(), t_double())), t_param("Distribution", &[t_double()])])),
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
