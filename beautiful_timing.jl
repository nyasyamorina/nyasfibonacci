using Plots


cd(@__DIR__)

# make sure the program is up to date
process = run(`cargo build --release`)
process.exitcode == 0 || @error "failed to build"

cd("./target/release/")

function timing(method_name, n)
    output_path = "timing.bin"
    process = run(`./nyasfibonacci.exe -m $method_name $n -o $output_path`)
    process.exitcode == 0 || (@error "failed to excute `nyasfibonacci.exe`"; return)

    open(output_path) do file
        time = read(file, Float64)
        @info "timing `$method_name::fibonacci($n)` in $time secs"
        time
    end
end

function find_target_timing(method_name, n0, n1, target)
    function break_cond(n0, n1, n2, t0, t1, target)
        allowable_error = 0.01
        if n1 >= n2
            n2
        elseif abs(t1 - target) <= allowable_error * target
            n1
        else
            nothing
        end
    end

    lnt2 = log(target)

    n0 < n1 || ((n0, n1) = (n1, n0))
    n0 == n1 && (@error "the two initial inputs cannot be equal"; return)

    t0 = timing(method_name, n0)
    lnt0 = log(t0)
    while true
        t1 = timing(method_name, n1)
        lnt1 = log(t1)

        n2 = if t0 < t1
            guess = (lnt2 - lnt1) / (lnt1 - lnt0) * (n1 - n0)
            n1 + round(typeof(n1), guess)
        else
            2n1 - n0
        end

        target_n = break_cond(n0, n1, n2, t0, t1, target)
        if target_n ≢ nothing
            return target_n
        else
            (n0, t0, lnt0, n1) = (n1, t1, lnt1, n2)
        end
    end
end


methods = [
    "recursion",
    "iteration",
]

recursion_axis = 0:38
recursion_time = timing.(Ref("recursion"), recursion_axis)
plot(recursion_axis, recursion_time; label = "recursion")
max_n = 38

target = find_target_timing("iteration", 60_000, 90_000, 1.2)
Δn = target ÷ 500
iteration_axis = 0:Δn:501Δn
iteration_time = timing.(Ref("iteration"), iteration_axis)
plot!(iteration_axis, iteration_time; label = "iteration")
max_n = max(max_n, last(iteration_axis))

plot!([0, max_n], [1, 1]; c = :black, lw = 2, label = false)
ylims!((0, 1.2))
