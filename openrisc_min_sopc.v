module openrisc_min_sopc(
	input wire clk,
	input wire rst
);

    wire[`InstAddrBus]  inst_addr;
    wire[`InstBus]      inst;
    wire                rom_ce;

    openrisc openrisc0(
		.clk(clk),
		.rst(rst),
		.rom_data_i(inst),
		.rom_addr_o(inst_addr),
		.rom_ce_o(rom_ce)
	);

	inst_rom inst_rom0(
		.addr(inst_addr),
		.ce(rom_ce),
		.inst(inst)
	);

endmodule
