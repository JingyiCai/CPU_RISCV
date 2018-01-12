module id(
	input wire                 rst,
	input wire[`InstAddrBus]   pc_i,
	input wire[`InstBus]       inst_i,

	input wire[`RegBus]        reg1_data_i,
	input wire[`RegBus]        reg2_data_i,

	//from ex
	input wire                 ex_wreg_i,
	input wire[`RegBus]        ex_wdata_i,
	input wire[`RegAddrBus]    ex_wd_i,

	//from mem
	input wire                 mem_wreg_i,
	input wire[`RegBus]        mem_wdata_i,
	input wire[`RegAddrBus]    mem_wd_i,

	output reg                 reg1_read_o,
	output reg                 reg2_read_o,
	output reg[`RegAddrBus]    reg1_addr_o,
	output reg[`RegAddrBus]    reg2_addr_o,

	output reg                 branch_flag_o,
	output reg[`RegBus]        branch_target_address_o,
	output reg[`RegBus]        link_addr_o,

	output reg[`AluOpBus]      aluop_o,
	output reg[`AluSelBus]     alusel_o,
	output reg[`RegBus]        reg1_o,
	output reg[`RegBus]        reg2_o,
	output reg[`RegAddrBus]    wd_o,
	output reg                 wreg_o
);

	wire[6:0] op_tp = inst_i[6:0];
	wire[4:0] op_rd = inst_i[11:7];
	wire[2:0] op1 = inst_i[14:12];
	wire[6:0] op2 = inst_i[31:25];
	wire[4:0] op_rs1 = inst_i[19:15];
	wire[4:0] op_rs2 = inst_i[24:20];
	reg[`RegBus] imm;
	reg instvalid;

	wire[`RegBus] pc_plus_4;
	wire[`RegBus] pc_plus_8;
	wire[`RegBus] imm_sll1_signedext;
    reg[`RegBus] rs2_mux;
    reg[`RegBus] result_sum;
    reg rs1_lt_rs2;
	assign pc_plus_4 = pc_i + 4;
	assign pc_plus_8 = pc_i + 8;
	assign imm_sll1_signedext = {inst_i[31], inst_i[7], inst_i[30:25], inst_i[11:8], 1'b0};

	always @ (*) begin
		if (rst == `RstEnable) begin
			aluop_o <= `EXE_NOP_OP;
			alusel_o <= `EXE_RES_NOP;
			wd_o <= `NOPRegAddr;
			wreg_o <= `WriteDisable;
			instvalid <= `InstValid;
			reg1_read_o <= 1'b0;
			reg2_read_o <= 1'b0;
			reg1_addr_o <= `NOPRegAddr;
			reg2_addr_o <= `NOPRegAddr;
			imm <= `ZeroWord;
			link_addr_o <= `ZeroWord;
			branch_flag_o <= `NotBranch;
			branch_target_address_o <= `ZeroWord;
		end else begin
			aluop_o <= `EXE_NOP_OP;
			alusel_o <= `EXE_RES_NOP;
			wd_o <= op_rd;
			wreg_o <= `WriteDisable;
			instvalid <= `InstInvalid;
			reg1_read_o <= 1'b0;
			reg2_read_o <= 1'b0;
			reg1_addr_o <= op_rs1;
			reg2_addr_o <= op_rs2;
			imm <= `ZeroWord;
			link_addr_o <= `ZeroWord;
			branch_flag_o <= `NotBranch;
			branch_target_address_o <= `ZeroWord;

			case (op_tp)
				`EXE_OP_IMM: begin
					case (op1)
						`EXE_ADDI: begin
							if (op_rd == `NOPRegAddr) begin
								aluop_o <= `EXE_NOP_OP;
								alusel_o <= `EXE_RES_NOP;
								wd_o <= `NOPRegAddr;
								wreg_o <= `WriteDisable;
								instvalid <= `InstValid;
								reg1_read_o <= 1'b0;
								reg2_read_o <= 1'b0;
								reg1_addr_o <= `NOPRegAddr;
								reg2_addr_o <= `NOPRegAddr;
								imm <= `ZeroWord;
							end else begin
						  		wreg_o <= `WriteEnable;
								aluop_o <= `EXE_ADD_OP;
								alusel_o <= `EXE_RES_ARITHMETIC;
								reg1_read_o <= 1'b1;
								reg2_read_o <= 1'b0;
								imm <= {{21{inst_i[31]}}, inst_i[30:20]};
								wd_o <= op_rd;
								instvalid <= `InstValid;
							end
					  	end
						`EXE_SLTI: begin
					  		wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLT_OP;
							alusel_o <= `EXE_RES_ARITHMETIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= {{21{inst_i[31]}}, inst_i[30:20]};
							wd_o <= op_rd;
							instvalid <= `InstValid;
					  	end
						`EXE_SLTIU: begin
					  		wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLTU_OP;
							alusel_o <= `EXE_RES_ARITHMETIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= {21'h0, inst_i[30:20]};
							wd_o <= op_rd;
							instvalid <= `InstValid;
					  	end
						`EXE_ANDI: begin
					  		wreg_o <= `WriteEnable;
							aluop_o <= `EXE_AND_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= {{21{inst_i[31]}}, inst_i[30:20]};
							wd_o <= op_rd;
							instvalid <= `InstValid;
					  	end
						`EXE_ORI: begin
					  		wreg_o <= `WriteEnable;
							aluop_o <= `EXE_OR_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= {{21{inst_i[31]}}, inst_i[30:20]};
							wd_o <= op_rd;
							instvalid <= `InstValid;
					  	end
						`EXE_XORI: begin
					  		wreg_o <= `WriteEnable;
							aluop_o <= `EXE_XOR_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= {{21{inst_i[31]}}, inst_i[30:20]};
							wd_o <= op_rd;
							instvalid <= `InstValid;
					  	end
						`EXE_SLLI: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLL_OP;
							alusel_o <= `EXE_RES_SHIFT;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							imm <= inst_i[24:20];
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_SRLI_SRAI: begin
							case (op2)
								`EXE_SRLI: begin
							  		wreg_o <= `WriteEnable;
									aluop_o <= `EXE_SRL_OP;
									alusel_o <= `EXE_RES_SHIFT;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b0;
									imm <= inst_i[24:20];
									wd_o <= op_rd;
									instvalid <= `InstValid;
							  	end
								`EXE_SRAI: begin
							  		wreg_o <= `WriteEnable;
									aluop_o <= `EXE_SRA_OP;
									alusel_o <= `EXE_RES_SHIFT;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b0;
									imm <= inst_i[24:20];
									wd_o <= op_rd;
									instvalid <= `InstValid;
							  	end
								default: begin
								end
							endcase
						end
						default: begin
						end
					endcase
				end
				`EXE_LUI: begin
					wreg_o <= `WriteEnable;
					aluop_o <= `EXE_LUI_OP;
					alusel_o <= `EXE_RES_LOGIC;
					reg1_read_o <= 1'b0;
					reg2_read_o <= 1'b0;
					imm <= {inst_i[31:12], 12'h0};
					wd_o <= op_rd;
					instvalid <= `InstValid;
				end
				`EXE_AUIPC: begin
					wreg_o <= `WriteEnable;
					aluop_o <= `EXE_AUIPC_OP;
					alusel_o <= `EXE_RES_LOGIC;
					reg1_read_o <= 1'b0;
					reg2_read_o <= 1'b0;
					imm <= pc_plus_4 + {inst_i[31:12], 12'h0};
					wd_o <= op_rd;
					instvalid <= `InstValid;
				end
				`EXE_OP: begin
					case (op1)
						`EXE_ADD_SUB: begin
							case (op2)
								`EXE_ADD: begin
									wreg_o <= `WriteEnable;
									aluop_o <= `EXE_ADD_OP;
									alusel_o <= `EXE_RES_ARITHMETIC;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b1;
									wd_o <= op_rd;
									instvalid <= `InstValid;
								end
								`EXE_SUB: begin
									wreg_o <= `WriteEnable;
									aluop_o <= `EXE_SUB_OP;
									alusel_o <= `EXE_RES_ARITHMETIC;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b1;
									wd_o <= op_rd;
									instvalid <= `InstValid;
								end
								default: begin
								end
							endcase
						end
						`EXE_SLT: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLT_OP;
							alusel_o <= `EXE_RES_ARITHMETIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_SLTU: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLTU_OP;
							alusel_o <= `EXE_RES_ARITHMETIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_AND: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_AND_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_OR: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_OR_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_XOR: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_XOR_OP;
							alusel_o <= `EXE_RES_LOGIC;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_SLL: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_SLL_OP;
							alusel_o <= `EXE_RES_SHIFT;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_SRL_SRA: begin
							case (op2)
								`EXE_SRL: begin
									wreg_o <= `WriteEnable;
									aluop_o <= `EXE_SRL_OP;
									alusel_o <= `EXE_RES_SHIFT;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b1;
									wd_o <= op_rd;
									instvalid <= `InstValid;
								end
								`EXE_SRA: begin
									wreg_o <= `WriteEnable;
									aluop_o <= `EXE_SRA_OP;
									alusel_o <= `EXE_RES_SHIFT;
									reg1_read_o <= 1'b1;
									reg2_read_o <= 1'b1;
									wd_o <= op_rd;
									instvalid <= `InstValid;
								end
								default: begin
								end
							endcase
						end
						default: begin
						end
					endcase
				end
				`EXE_JAL: begin
					wreg_o <= `WriteEnable;
					aluop_o <= `EXE_JAL_OP;
					alusel_o <= `EXE_RES_JUMP_BRANCH;
					reg1_read_o <= 1'b0;
					reg2_read_o <= 1'b0;
					wd_o <= op_rd;
					instvalid <= `InstValid;
					link_addr_o <= pc_plus_4;
					branch_flag_o <= `Branch;
					branch_target_address_o <= pc_plus_4 + {{12{inst_i[31]}}, inst_i[19:12], inst_i[20], inst_i[30:21], 1'b0};
				end
				`EXE_JALR: begin
					wreg_o <= `WriteEnable;
					aluop_o <= `EXE_JALR_OP;
					alusel_o <= `EXE_RES_JUMP_BRANCH;
					reg1_read_o <= 1'b1;
					reg2_read_o <= 1'b0;
					wd_o <= op_rd;
					instvalid <= `InstValid;
					link_addr_o <= pc_plus_4;
					branch_flag_o <= `Branch;
					branch_target_address_o <= (inst_i[31:20] + op_rs1) & (1'b0);
				end
				`EXE_BRANCH: begin
					rs2_mux = (~op_rs2) + 1;
					result_sum = op_rs1 + rs2_mux;
					rs1_lt_rs2 = ((op_rs1[4] && !op_rs2[4]) ||
										 (!op_rs1[4] && !op_rs2[4] && result_sum[4]) ||
										 (op_rs1[4] && op_rs2[4] && result_sum[4]));

					case (op1)
						`EXE_BEQ: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BEQ_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (op_rs1 == op_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						`EXE_BNE: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BNE_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (op_rs1 != op_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						`EXE_BLT: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BLT_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (rs1_lt_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						`EXE_BLTU: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BLT_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (op_rs1 < op_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						`EXE_BGE: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BGE_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (!rs1_lt_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						`EXE_BGEU: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_BGE_OP;
							alusel_o <= `EXE_RES_JUMP_BRANCH;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
							if (op_rs1 > op_rs2) begin
								branch_flag_o <= `Branch;
								branch_target_address_o <= pc_plus_4 + imm_sll1_signedext;
							end
						end
						default: begin
						end
					endcase
				end
				`EXE_LOAD: begin
					case (op1)
						`EXE_LB: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_LB_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_LH: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_LH_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_LW: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_LW_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_LBU: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_LBU_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						`EXE_LHU: begin
							wreg_o <= `WriteEnable;
							aluop_o <= `EXE_LHU_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b0;
							wd_o <= op_rd;
							instvalid <= `InstValid;
						end
						default: begin
						end
					endcase
				end
				`EXE_STORE: begin
					case (op1)
						`EXE_SB: begin
							wreg_o <= `WriteDisable;
							aluop_o <= `EXE_SB_OP;
							alusel_o <= `EXE_RES_LOAD_STORE;
							reg1_read_o <= 1'b1;
							reg2_read_o <= 1'b1;
							instvalid <= `InstValid;
						end
						default: begin
						end
					endcase
				end
				default: begin
				end
			endcase
		end
	end

	always @ (*) begin
		if (rst == `RstEnable) begin
			reg1_o <= `ZeroWord;
		end else if ((reg1_read_o == 1'b1) && (ex_wreg_i == 1'b1)
									&& (ex_wd_i == reg1_addr_o)) begin
			reg1_o <= ex_wdata_i;
		end else if ((reg1_read_o == 1'b1) && (mem_wreg_i == 1'b1)
									&& (mem_wd_i == reg1_addr_o)) begin
			reg1_o <= ex_wdata_i;
		end else if (reg1_read_o == 1'b1) begin
			reg1_o <= reg1_data_i;
		end else if (reg1_read_o == 1'b0) begin
			reg1_o <= imm;
		end else begin
			reg1_o <= `ZeroWord;
		end
	end

	always @ (*) begin
		if (rst == `RstEnable) begin
			reg2_o <= `ZeroWord;
		end else if ((reg2_read_o == 1'b1) && (ex_wreg_i == 1'b1)
									&& (ex_wd_i == reg2_addr_o)) begin
			reg2_o <= ex_wdata_i;
		end else if ((reg2_read_o == 1'b1) && (mem_wreg_i == 1'b1)
									&& (mem_wd_i == reg2_addr_o)) begin
			reg2_o <= ex_wdata_i;
		end else if (reg2_read_o == 1'b1) begin
			reg2_o <= reg2_data_i;
		end else if (reg2_read_o == 1'b0) begin
			reg2_o <= imm;
		end else begin
			reg2_o <= `ZeroWord;
		end
	end

endmodule
