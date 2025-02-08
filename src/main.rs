use std::{
    env::{args, Args},
    fs::File,
    hint::black_box,
    io::Write,
    time::{Duration, Instant},
};

use nyasfibonacci::*;

static FIBONACCIS: &[(&str, fn(u64) -> UBig)] = &[
    ("recursion", recursion::fibonacci),
    ("iteration", iteration::fibonacci),
    ("matrix_pow", matrix_pow::fibonacci::<ElementarySchoolMul>),
    ("small_matrix", small_matrix::fibonacci::<ElementarySchoolMul>),
    ("rev_pow", rev_pow::fibonacci::<ElementarySchoolMul>),
    ("removed_abstract", rev_pow::fibonacci_removed_matrix_abstract::<ElementarySchoolMul>),
    ("matrix_pow_karatsuba", matrix_pow::fibonacci::<KaratsubaMul>),
    ("small_matrix_karatsuba", small_matrix::fibonacci::<KaratsubaMul>),
    ("rev_pow_karatsuba", rev_pow::fibonacci::<KaratsubaMul>),
];

#[derive(Debug)]
struct CommandLineOptions {
    print_help: bool,
    list_methods: bool,
    target_method: Option<String>,
    n: u64,
    output_number: bool,
    output_path: Option<String>,
}
impl CommandLineOptions {
    fn parse(args: Args) -> Self {
        let mut opts = CommandLineOptions {
            print_help: false,
            output_path: None,
            n: 0,
            target_method: None,
            output_number: false,
            list_methods: false,
        };

        let mut iter = args.into_iter();
        while let Some(arg) = iter.next() {
            if arg == "-h" || arg == "--help" {
                opts.print_help = true;
            } else if arg == "-o" || arg == "--output" {
                match iter.next() {
                    None => {}
                    Some(path) => opts.output_path = Some(path),
                }
            } else if arg == "-m" || arg == "--method" {
                match iter.next() {
                    None => panic!(
                        "expect a method name after `{}`, you can use `-l` to show all methods",
                        arg
                    ),
                    Some(method) => opts.target_method = Some(method),
                }

                let mut got_number = false;
                if let Some(num) = iter.next() {
                    if let Ok(num) = num.parse() {
                        opts.n = num;
                        got_number = true;
                    }
                }
                if !got_number {
                    panic!("expect a non-negative integer number after method name")
                }
            } else if arg == "-l" || arg == "--list" {
                opts.list_methods = true;
            } else if arg == "--output-number" {
                opts.output_number = true;
            }
        }

        opts
    }
}

fn main() {
    let opts = CommandLineOptions::parse(args());

    if opts.print_help {
        print_help();
    } else if opts.list_methods {
        list_methods(opts.output_path);
    } else if let Some(method_name) = opts.target_method {
        time_and_report(method_name, opts.n, opts.output_path, opts.output_number);
    }
}

fn print_help() {
    println!("command line arguments:");
    println!(" -h | --help                    print this");
    println!(" -l | --list                    list all available methods");
    println!(" -m | --method <method> <n>     timing a method with input n");
    println!(" --output-number                print the fibonacci number");
    println!(" -o | --output [file path]      output the timing result and the fibonacci");
    println!("                                number (if enabled) to specific file");
    println!();
    println!("output to file format:");
    println!(" - data in file:        only contains `method_names` if `-l` is enabled");
    println!("       [method_names] | [timing_result]");
    println!(" - method_names:");
    println!("       [method_name...]");
    println!(" - method_name:         encoded with utf-8");
    println!("       <name: string><'\\n'>");
    println!(" - timing_result:       contains `number` if `--output_number` is enabled");
    println!("       <sec: f64>[number]");
    println!(" - number:              the length of `u64...` is equal to `u64s`");
    println!("       <u64s: u64>[u64...]");
    println!();
}

fn list_methods(path: Option<String>) {
    if let Some(path) = path {
        let mut file = File::create(path).unwrap();
        for (method_name, _) in FIBONACCIS {
            file.write_fmt(format_args!("{}\n", method_name)).unwrap();
        }
    } else {
        println!("methods:");
        for (method_name, _) in FIBONACCIS {
            println!(" - {}", method_name);
        }
        println!();
    }
}

fn time_and_report(method_name: String, n: u64, path: Option<String>, output_number: bool) {
    let mut iter = FIBONACCIS.iter();
    let method = loop {
        if let Some((name, method)) = iter.next() {
            if &method_name == name {
                break method;
            }
        } else {
            panic!(
                "cannot find method named {}, use `-l` to list all available methods",
                method_name
            );
        }
    };

    let (number, dur) = timing(method, n);
    let dur = dur.as_secs_f64();

    if let Some(path) = path {
        let mut file = File::create(path).unwrap();
        file.write_all(&dur.to_ne_bytes()).unwrap();
        if output_number {
            let vec = number.to_vec();
            let len = vec.len() as u64;
            file.write_all(&len.to_ne_bytes()).unwrap();
            vec.iter()
                .for_each(|x| file.write_all(&x.to_ne_bytes()).unwrap());
        }
    } else {
        println!("timing result: {} secs", dur);
        if output_number {
            println!("output number: {}", number);
        }
        println!();
    }
}

fn timing<F: Fn(u64) -> UBig>(fib: &F, n: u64) -> (UBig, Duration) {
    let start = Instant::now();

    let out = black_box(fib(black_box(n)));

    let dur = start.elapsed();
    (out, dur)
}
