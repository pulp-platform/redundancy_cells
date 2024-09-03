// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 09.09.2024
// Description: Interface in between time_DMR modules to transmit which elements are valid

interface time_DMR_interface #(
  parameter IDSize = 0,
  // Determines if the internal state machines should
  // be parallely redundant, meaning errors inside this module
  // can also not cause errors in the output
  // The external output is never protected!
  parameter bit InternalRedundancy = 0,
  // Do not modify
  localparam int REP = InternalRedundancy ? 3 : 1
) ( 
  /* No ports on this interface */ 
);
    logic [REP-1:0][IDSize-1:0] id;
    logic [REP-1:0] sent;

    modport sender (
      input id,
      input sent
    );

    modport reciever (
      output id,
      output sent
    );
endinterface