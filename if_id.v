module if_id(
    input wire clk,
    input wire rst,

    input wire[`InstAddrBus] if_pc,
    input wire[`InstBus] if_inst,

    output reg[`InstAddrBus] id_pc,
    output reg[`InstBus] id_inst
);

    always @ (posedge clk) begin
        if (rst == `RstEnable) begin
            id_pc <= `ZeroWord;
            id_inst <= `ZeroWord;
        end else begin
            id_pc <= if_pc;
            id_inst <= {if_inst[7:0], if_inst[15:8], if_inst[23:16], if_inst[31:24]};
        end
    end

endmodule
