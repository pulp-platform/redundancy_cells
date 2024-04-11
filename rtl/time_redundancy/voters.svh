
`define MAJORITY(a, b, c, o) \
begin \
    o = (a & b) | (a & c) | (b & c); \
end

`define BITWISE(a) \
    a[$bits(a)-1:0]

`define VOTE3to3(input_signal, output_signal) \
always_comb begin \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[0]); \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[1]); \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal[2]); \
end

`define VOTE3to3ENUM(input_signal, output_signal) \
always_comb begin \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[0])); \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[1])); \
    `MAJORITY(`BITWISE(input_signal[0]), `BITWISE(input_signal[1]), `BITWISE(input_signal[2]),  `BITWISE(output_signal[2])); \
end

`define VOTE3to1(input_signal, output_signal) \
always_comb begin \
    `MAJORITY(input_signal[0], input_signal[1], input_signal[2],  output_signal); \
end
