using Printf


function print_ubig(x::BigInt, N)
    for index ∈ 0:N
        index % 8 == 0 && print("\n    ")
        (d, x) = divrem(x, u64^(N-index))
        Printf.@printf "%016X_" d
    end
end


const u64 = BigInt(2)^64

struct SsaStep
    l::UInt64
    n::UInt64
    y::UInt64
    N::UInt64
    M::UInt64
    L::UInt64
end
function SsaStep(min_len)::Union{Nothing, SsaStep}
    min_len < 16 && return nothing

    l = floor(UInt64, 0.5 * (1 + log2(min_len)))
    n = ceil(UInt64, min_len / 2.0^l)
    y = ceil(UInt64, (l + 2n) / 2.0^l)
    SsaStep(l, n, y, n << l, y << l, 1 << l)
end

function print_num(step::SsaStep, num::BigInt)
    print("---- num begin")
    print_ubig(num, step.N)
    println("\n---- num end")
end

function print_arr(step::SsaStep, arr::AbstractVector{BigInt})
    print("---- arr begin")
    for (k, ele) ∈ enumerate(arr)
        print("\n  -- $(k-1)")
        print_ubig(ele, step.M)
    end
    println("\n---- arr end")
end

function print_ele(step::SsaStep, ele::BigInt)
    print("---- ele begin")
    print_ubig(ele, step.M)
    println("\n---- ele end")
end


function divide_num_to_arr(step::SsaStep, num::BigInt)::Vector{BigInt}
    arr = Vector{BigInt}(undef, 0)
    while length(arr) < (1 << step.l)
        push!(arr, num & (u64^step.n - 1))
        num = num >> (64*step.n)
    end
    arr
end

function combine_arr_to_num(step::SsaStep, arr::Vector{BigInt})::BigInt
    num_ring = u64^step.N + 1
    x = zero(BigInt)
    for k ∈ eachindex(arr)
        C_k = if arr[k] > k * u64^(step.n << 1)
            C_k = arr[k] - 1
            C_k - u64^step.M
        else
            arr[k]
        end
        x = mod(x + C_k * u64^((k - 1) * step.n), num_ring)
    end
    x
end

function shift_in(step::SsaStep, ele::BigInt, k)::BigInt
    ele_ring = u64^step.M + 1
    mod(ele << (64 * k * step.y), ele_ring)
end

function shift_out(step::SsaStep, ele::BigInt, k)::BigInt
    ele_ring = u64^step.M + 1
    inv_y = 2step.M - step.y
    mod(ele << (64 * k * inv_y), ele_ring)
end

function fft!(step::SsaStep, arr::AbstractVector{BigInt})
    reindex_fft_eles!(step, arr)
    radix_2!(step, arr, 2step.y)
end

function ifft!(step::SsaStep, arr::AbstractVector{BigInt})
    reindex_fft_eles!(step, arr)
    radix_2!(step, arr, 2(step.M - step.y))
end

function reindex_fft_eles!(step::SsaStep, arr::Vector{BigInt})
    for k ∈ 1:step.L
        l = (reverse_bits(k - 1) >> (64 - step.l)) + 1
        l > k && ((arr[k], arr[l]) = (arr[l], arr[k]))
    end
end

function reverse_bits(x::UInt64)::UInt64
    x = ((x & 0xFFFFFFFF00000000) >> 32) | ((x & 0x00000000FFFFFFFF) << 32)
    x = ((x & 0xFFFF0000FFFF0000) >> 16) | ((x & 0x0000FFFF0000FFFF) << 16)
    x = ((x & 0xFF00FF00FF00FF00) >>  8) | ((x & 0x00FF00FF00FF00FF) <<  8)
    x = ((x & 0xF0F0F0F0F0F0F0F0) >>  4) | ((x & 0x0F0F0F0F0F0F0F0F) <<  4)
    x = ((x & 0xCCCCCCCCCCCCCCCC) >>  2) | ((x & 0x3333333333333333) <<  2)
    x = ((x & 0xAAAAAAAAAAAAAAAA) >>  1) | ((x & 0x5555555555555555) <<  1)
    x
end

function radix_2!(step::SsaStep, arr::AbstractVector{BigInt}, root)
    ele_ring = u64^step.M + 1
    half_len = length(arr) ÷ 2
    E = @view arr[1:half_len]
    O = @view arr[(half_len+1):end]

    if half_len > 1
        radix_2!(step, E, root << 1)
        radix_2!(step, O, root << 1)
    end

    for k ∈ 1:half_len
        tmp = mod(O[k] * u64^((k - 1) * root), ele_ring)
        O[k] = mod(E[k] - tmp, ele_ring)
        E[k] = mod(E[k] + tmp, ele_ring)
    end
end

function div_by_arr_len(step::SsaStep, ele::BigInt)::BigInt
    ele_ring = u64^step.M + 1
    log2_inv_arr_len = 64 * (2step.M) - step.l
    mod(ele << log2_inv_arr_len, ele_ring)
end

function ssa_sqr_exec(num::BigInt, N, steps::Vector{SsaStep}, depth)::BigInt
    num >= u64^N #= x = u64^N ≡ -1 =# && return 1
    (depth ∈ eachindex(steps) && N > 30) || return mod(num^2, u64^N+1)
    step = steps[depth]

    arr = divide_num_to_arr(step, num)

    for k ∈ eachindex(arr)
        arr[k] = shift_in(step, arr[k], k - 1)
    end
    fft!(step, arr)

    for k ∈ eachindex(arr)
        arr[k] = ssa_sqr_exec(arr[k], step.M, steps, depth + 1)
    end

    ifft!(step, arr)
    for k ∈ eachindex(arr)
        arr[k] = div_by_arr_len(step, arr[k])
        arr[k] = shift_out(step, arr[k], k - 1)
    end

    combine_arr_to_num(step, arr)
end

function ssa_sqr(x::BigInt, len)
    steps = Vector{SsaStep}(undef, 0)
    N = len
    while true
        step = SsaStep(N)
        step ≡ nothing && break
        push!(steps, step)
        N = step.y << step.l
    end

    ssa_sqr_exec(x, len, steps, 1)
end
