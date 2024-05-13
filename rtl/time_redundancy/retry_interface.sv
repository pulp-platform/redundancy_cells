// Author: Maurus Item <itemm@student.ethz.ch>, ETH Zurich
// Date: 25.04.2024
// Description: Interface in between retry modules to transmit which elements need to be tried again

interface retry_interface #(parameter IDSize = 0) ( /* No ports on this interface */ );
    logic [IDSize-1:0] id;
    logic valid;
    logic ready;
    logic [IDSize-1:0] id_feedback;
    logic lock;

    modport start (
      input id,
      input valid,
      output ready,
      output id_feedback,
      input lock
    );

    modport ende (
      output id,
      output valid,
      input ready,
      input id_feedback,
      output lock
    );
endinterface