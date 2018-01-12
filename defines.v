`define RstEnable 1'b1
`define RstDisable 1'b0
`define ZeroWord 32'h00000000
`define WriteEnable 1'b1
`define WriteDisable 1'b0
`define ReadEnable 1'b1
`define ReadDisable 1'b0
`define AluOpBus 7:0
`define AluSelBus 2:0
`define InstValid 1'b0
`define InstInvalid 1'b1
`define Stop 1'b1
`define NoStop 1'b0
`define InDelaySlot 1'b1
`define NotInDelaySlot 1'b0
`define Branch 1'b1
`define NotBranch 1'b0
`define InterruptAssert 1'b1
`define InterruptNotAssert 1'b0
`define TrapAssert 1'b1
`define TrapNotAssert 1'b0
`define True_v 1'b1
`define False_v 1'b0
`define ChipEnable 1'b1
`define ChipDisable 1'b0


`define Stop 1'b1
`define NotStop 1'b0
`define Branch 1'b1
`define NotBranch 1'b0


`define EXE_OP_IMM      7'b0010011
`define EXE_LUI         7'b0110111
`define EXE_AUIPC       7'b0010111
`define EXE_OP          7'b0110011
`define EXE_JAL         7'b1101111
`define EXE_JALR        7'b1100111
`define EXE_BRANCH      7'b1100011
`define EXE_LOAD        7'b0000011
`define EXE_STORE       7'b0100011


`define EXE_ADDI        3'b000
`define EXE_SLTI        3'b010
`define EXE_ANDI        3'b111
`define EXE_SLTIU       3'b011
`define EXE_ORI         3'b110
`define EXE_XORI        3'b100
`define EXE_SLLI        3'b001
`define EXE_SRLI_SRAI   3'b101
`define EXE_SRLI        7'b0000000
`define EXE_SRAI        7'b0100000

`define EXE_ADD_SUB     3'b000
`define EXE_ADD         7'b0000000
`define EXE_SUB         7'b0100000
`define EXE_SLT         3'b010
`define EXE_SLTU        3'b011
`define EXE_AND         3'b111
`define EXE_OR          3'b110
`define EXE_XOR         3'b100
`define EXE_SLL			3'b001
`define EXE_SRL_SRA     3'b101
`define EXE_SRL         7'b0000000
`define EXE_SRA         7'b0100000

`define EXE_BEQ         3'b000
`define EXE_BNE         3'b001
`define EXE_BLT         3'b100
`define EXE_BLTU        3'b110
`define EXE_BGE         3'b101
`define EXE_BGEU        3'b111

`define EXE_LB          3'b000
`define EXE_LH          3'b001
`define EXE_LW          3'b010
`define EXE_LBU         3'b100
`define EXE_LHU         3'b101
`define EXE_SB          3'b000
`define EXE_SH          3'b001
`define EXE_SW          3'b010

`define EXE_NOP         3'b000


`define EXE_ADD_OP      8'b00000001
`define EXE_SUB_OP      8'b00000010
`define EXE_SLT_OP      8'b00000100
`define EXE_SLTU_OP     8'b00011000
`define EXE_AND_OP      8'b00001000
`define EXE_OR_OP       8'b00010000
`define EXE_XOR_OP      8'b00100000
`define EXE_SLL_OP      8'b01000000
`define EXE_SRL_OP      8'b10000000
`define EXE_SRA_OP      8'b00000011
`define EXE_LUI_OP      8'b00000110
`define EXE_AUIPC_OP    8'b00001100

`define EXE_JAL_OP      8'b00001010
`define EXE_JALR_OP     8'b00010100
`define EXE_BEQ_OP      8'b00110000
`define EXE_BNE_OP      8'b01100000
`define EXE_BLT_OP      8'b11000000
`define EXE_BGE_OP      8'b00000101

`define EXE_LB_OP       8'b00101000
`define EXE_LH_OP       8'b01010000
`define EXE_LW_OP       8'b10100000
`define EXE_LBU_OP      8'b00000111
`define EXE_LHU_OP      8'b00001110
`define EXE_SB_OP       8'b00011100
`define EXE_SH_OP       8'b00111000
`define EXE_SW_OP       8'b01110000

`define EXE_NOP_OP      8'b00000000


`define EXE_RES_ARITHMETIC 3'b100
`define EXE_RES_LOGIC 3'b001
`define EXE_RES_SHIFT 3'b010
`define EXE_RES_JUMP_BRANCH 3'b011
`define EXE_RES_LOAD_STORE 3'b110
`define EXE_RES_NOP 3'b000


`define InstAddrBus 31:0
`define InstBus 31:0
`define InstMemNum 131071
`define InstMemNumLog2 17


`define DataAddrBus 31:0
`define DataBus 31:0
`define DataMemNum 131071
`define DataMemNumLog2 17
`define ByteWidth 7:0


`define RegAddrBus 4:0
`define RegBus 31:0
`define RegWidth 3244
`define RegNum 32
`define RegNumLog2 5
`define NOPRegAddr 5'b00000
