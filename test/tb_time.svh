//////////////////////////////////////////////////////////////////////////////////7
// Signal Definitions
//////////////////////////////////////////////////////////////////////////////////7

logic clk, rst_n;
logic valid_in, ready_in;
logic valid_out, ready_out;
logic enable;

//////////////////////////////////////////////////////////////////////////////////7
// Initial State
//////////////////////////////////////////////////////////////////////////////////7
initial clk         = 1'b0;
initial rst_n       = 1'b1;
initial valid_in    = 1'b0;
initial ready_out   = 1'b0;
initial enable      = 1'b0;

//////////////////////////////////////////////////////////////////////////////////7
// Clock Setup
//////////////////////////////////////////////////////////////////////////////////7
longint unsigned reset_length = 20;

always #((CLK_PERIOD/2)) clk = ~clk;

task reset();
    rst_n = 1'b0;
    repeat (reset_length) @(negedge clk);
    rst_n = 1'b1;
endtask

//////////////////////////////////////////////////////////////////////////////////7
// Handshake setup
//////////////////////////////////////////////////////////////////////////////////7
longint unsigned in_hs_count = 0;
longint unsigned in_hs_max_starvation = 5;

longint unsigned out_hs_count = 0;
longint unsigned out_hs_max_starvation = 5;

task input_handshake_begin();
    // Wait random time (with no valid data)
    repeat ($urandom_range(0, in_hs_max_starvation)) begin
        @(posedge clk);
        #APPLICATION_DELAY;
    end

    // Wait for reset to pass
    while (!rst_n) begin
        @(posedge clk) ;
        #APPLICATION_DELAY;
    end
endtask

task  input_handshake_end();
    // Perform Handshake
    valid_in = 1'b1;  

    # (AQUISITION_DELAY - APPLICATION_DELAY);
    while (!ready_in) begin
        @(posedge clk);
        # AQUISITION_DELAY;
    end
    @(posedge clk);                 
    # APPLICATION_DELAY;
    valid_in = 1'b0; // This might get overwritten by next handshake

    in_hs_count  = in_hs_count + 1;
endtask

task output_handshake_start();
    // Wait random time (with no valid data)
    repeat ($urandom_range(0, out_hs_max_starvation)) begin
        @(posedge clk); 
        # APPLICATION_DELAY;
    end

    // Wait for reset to pass
    while (!rst_n) begin
        @(posedge clk); 
        # APPLICATION_DELAY;
    end

    ready_out = 1'b1;

    // Wait for correct amount of time in cycle
    # (AQUISITION_DELAY - APPLICATION_DELAY);
    while (!valid_out) begin
        @(posedge clk); 
        #AQUISITION_DELAY;
    end
endtask

task output_handshake_end();
    @(posedge clk);
    # APPLICATION_DELAY;
    ready_out = 1'b0; // This might get overwritten by next handshake

    out_hs_count  = out_hs_count + 1;
endtask