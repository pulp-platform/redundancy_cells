// Macros to instantiate some kind of Voters
// If you want to use different kinds of Cells, you only have to change these
`define TMR_INSTANCE(input_signal, output_signal, instance_name) \
bitwise_TMR_voter_fail #(.DataWidth($bits(input_signal[0])), .VoterType(2)) instance_name ( \
  .a_i(input_signal[0]), \
  .b_i(input_signal[1]), \
  .c_i(input_signal[2]), \
  .majority_o(output_signal), \
  .fault_detected_o() \
);

`define TMR_INSTANCE_F(input_signal, output_signal, fault_any, instance_name) \
bitwise_TMR_voter_fail #(.DataWidth($bits(input_signal[0])), .VoterType(1)) instance_name ( \
  .a_i(input_signal[0]), \
  .b_i(input_signal[1]), \
  .c_i(input_signal[2]), \
  .majority_o(output_signal), \
  .fault_detected_o(fault_any) \
);

`define TMR_INSTANCE_W(input_signal, output_signal, fault_210, fault_multiple, instance_name) \
bitwise_TMR_voter #(.DataWidth($bits(input_signal[0])), .VoterType(2)) instance_name ( \
  .a_i(input_signal[0]), \
  .b_i(input_signal[1]), \
  .c_i(input_signal[2]), \
  .majority_o(output_signal), \
  .error_o(fault_multiple), \
  .error_cba_o(fault_210) \
);

// Macro to create a name based on the current line in the file
// Name looks like: base_name_L42
`define UNIQUE_NAME(base_name) ``base_name``_L```__LINE__

// 3 -> 1 Voters
`define VOTE31(input_signal, output_signal) \
`TMR_INSTANCE(input_signal, output_signal, `UNIQUE_NAME(i_bitwise_TMR_voter_fail));

`define VOTE31F(input_signal, output_signal, fault_any) \
`TMR_INSTANCE_F(input_signal, output_signal, fault_any, `UNIQUE_NAME(i_bitwise_TMR_voter_fail));

`define VOTE31W(input_signal, output_signal, fault_210, fault_multiple) \
`TMR_INSTANCE_W(input_signal, output_signal, fault_210, fault_multiple, `UNIQUE_NAME(i_bitwise_TMR_voter));


// 3 -> 3 Voters
`define VOTE33(input_signal, output_signal) \
`TMR_INSTANCE(input_signal, output_signal[0], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_0)); \
`TMR_INSTANCE(input_signal, output_signal[1], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_1)); \
`TMR_INSTANCE(input_signal, output_signal[2], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_2));

`define VOTE33F(input_signal, output_signal, fault_any) \
`TMR_INSTANCE_F(input_signal, output_signal[0], fault_any, `UNIQUE_NAME(i_bitwise_TMR_voter_fail_0f)); \
`TMR_INSTANCE(input_signal, output_signal[1], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_1)); \
`TMR_INSTANCE(input_signal, output_signal[2], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_2));

`define VOTE33W(input_signal, output_signal, fault_210, fault_multiple) \
`TMR_INSTANCE_W(input_signal, output_signal[0], fault_210, fault_multiple, `UNIQUE_NAME(i_bitwise_TMR_voter_fail_0w)); \
`TMR_INSTANCE(input_signal, output_signal[1], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_1)); \
`TMR_INSTANCE(input_signal, output_signal[2], `UNIQUE_NAME(i_bitwise_TMR_voter_fail_2));


// localparam REP -> 1 Voters 
`define VOTEX1(input_signal, output_signal) \
if (REP == 3) begin \
    `VOTE31(input_signal, output_signal); \
end else if (REP == 2) begin \
    assign output_signal = input_signal[0]; \
end else begin \
    assign output_signal = input_signal[0]; \
end

`define VOTEX1F(input_signal, output_signal, fault_any) \
if (REP == 3) begin \
    `VOTE31F(input_signal, output_signal, fault_any); \
end else if (REP == 2) begin \
    assign output_signal = input_signal[0]; \
    assign fault_any = input_signal[0] != input_signal[1]; \
end else begin \
    assign output_signal = input_signal[0]; \
    assign fault_any = 1'b1; \
end


// localparam REP -> REP Voters 
`define VOTEXX(input_signal, output_signal) \
if (REP == 3) begin \
    `VOTE33(input_signal, output_signal); \
end else if (REP == 2) begin \
    assign output_signal = input_signal; \
end else begin \
    assign output_signal = input_signal; \
end

`define VOTEXXF(input_signal, output_signal, fault_any) \
if (REP == 3) begin \
    `VOTE33F(input_signal, output_signal, fault_any); \
end else if (REP == 2) begin \
    assign output_signal = input_signal; \
    assign fault_any = input_signal[0] != input_signal[1]; \
end else begin \
    assign output_signal = input_signal; \
    assign fault_any = 1'b1; \
end
