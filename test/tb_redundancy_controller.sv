module tb_redundancy_controller #(
    // DUT Parameters
    parameter bit InternalRedundancy = 0,

    // TB Parameters
    parameter int unsigned TESTS = 10,
    parameter time CLK_PERIOD = 10ns,
    parameter time APPLICATION_DELAY = 2ns,
    parameter time AQUISITION_DELAY = 8ns

) ( /* no ports on TB */ );

	// Signals for dut
	logic clk_i;
    logic rst_ni;

    // Connection to outside
    logic enable_i;
    logic busy_o;

    // Connection to redundancy modules
    logic busy_i;
    logic enable_o;

    // Upstream Handshake
    logic valid_i;
    logic ready_o;

    // Downstream Handshake
    logic valid_o;
    logic ready_i;

	// Dut
	redundancy_controller # (
	    .InternalRedundancy(InternalRedundancy)
	) i_dut (
	    .*
	); 

	initial clk_i = 0;
	initial rst_ni = 1;
	always #((CLK_PERIOD/2)) clk_i = ~clk_i;

	task check_handshake_passthrough();
		valid_i = $random;
		ready_i = $random;
		# (AQUISITION_DELAY - APPLICATION_DELAY);
		assert(valid_o == valid_i);
		assert(ready_o == ready_o);
		assert(enable_o == enable_i);
	endtask

	task check_handshake_blocked();
		valid_i = $random;
		ready_i = $random;
		# (AQUISITION_DELAY - APPLICATION_DELAY);
		assert(valid_o == 0);
		assert(ready_o == 0);
		assert(enable_o != enable_i);
	endtask


	initial begin
		// Start state
		enable_i = 0;
		busy_i = 0;

		repeat (TESTS) begin
			@(posedge clk_i);
			# APPLICATION_DELAY;
			busy_i = 1;
			enable_i = ~enable_i;

			repeat ($urandom_range(0, 5)) begin
		        check_handshake_blocked();
		        @(posedge clk_i);
		        #APPLICATION_DELAY;
		    end

			@(posedge clk_i);
			# APPLICATION_DELAY;
		    busy_i = 0;
		    check_handshake_blocked();

			repeat (5) begin
				@(posedge clk_i);
		        #APPLICATION_DELAY;
				check_handshake_passthrough();
			end

		end
		$finish;
	end

endmodule