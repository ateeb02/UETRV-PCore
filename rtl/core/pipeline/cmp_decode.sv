// Copyright 2023 University of Engineering and Technology Lahore.
// Licensed under the Apache License, Version 2.0, see LICENSE file for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: 16-bit to 32-bit Compressed Instruction Decoder.
//
// Author: Ateeb Tahir
// Date: 1.16.2024

module cmp_decode (
	input wire  [`XLEN-1:0]                          inst16_i,
	output                                          inst32_o,

	input wire                                      req_i
);

localparam OPCODE_LOAD     = 7'h03;
localparam OPCODE_OP_IMM   = 7'h13;
localparam OPCODE_STORE    = 7'h23;
localparam OPCODE_OP       = 7'h33;
localparam OPCODE_LUI      = 7'h37;
localparam OPCODE_BRANCH   = 7'h63;
localparam OPCODE_JALR     = 7'h67;
localparam OPCODE_JAL      = 7'h6f;

logic 	[15:0]          	inst16;
logic   [`XLEN-1:0]         inst32;
logic 						illegal_instr;

logic   [`XLEN-1:0]         c_addi4spn_2_addi, c_addi_2_addi, c_addi16sp_2_addi, 
							c_li_2_addi, c_lui_2_lui, c_add_2_add, c_mv_2_add, 
							c_sub_2_sub, c_lw_2_lw, c_lwsp_2_lw, c_sw_2_sw, 
							c_swsp_2_sw, c_jal_2_jal, c_jr_2_jalr,c_jalr_2_jalr, 
							c_xor_2_xor, c_or_2_or, c_and_2_and, c_andi_2_andi, 
							c_slli_2_slli, c_srli_2_srli, c_beqz_2_beq, 
							c_ebreak_2_ebreak;

assign inst16 = inst16_i;

always_comb begin
	illegal_instr     = 1'b0;
	case (inst16[1:0])
	2'b00: begin
		case (inst16[15:14])
		2'b00: begin inst32 = c_addi4spn_to_addi;   end
		2'b01: begin inst32 = c_lw_2_lw;            end
		2'b11: begin inst32 = c_sw_2_sw;            end
		2'b10: begin illegal_instr = 1'b1; inst32 = 32'h13; end
		endcase
	end 2'b01: begin
		case (inst16[15:13])
		3'b000: begin inst32 = c_addi_2_addi;       end
		//c_jal and c_jalr
		3'b001, 3'b101: begin inst32 = c_jal_2_jal; end
		3'b010: begin inst32 = c_li_2_addi;         end
		3'b011: begin
			// c_lui to lui or c_addi16sp to addi
			inst32 = (inst16[11:7] == 5'h02) ? c_addi16sp_2_addi : c_lui_2_lui; end
		3'b100: begin
			case (inst16[11:10])
			2'b00, 2'b01: begin inst32 = c_srli_2_srli; end
			2'b10: begin inst32 = c_andi_2_andi;    end
			2'b11: begin
				case (inst16[6:5])
				2'b00: begin inst32 = c_sub_2_sub;  end
				2'b01: begin inst32 = c_xor_2_xor;  end
				2'b10: begin inst32 = c_or_2_or;    end
				2'b11: begin inst32 = c_and_2_and;  end
				endcase
			end
			endcase
		end
		// c_beqz and c_bnez to beq and bne
		3'b110, 3'b111: begin inst32 = c_beqz_2_beq; end
		endcase
	end 2'b10: begin
		case (inst16[15:14])
		2'b00: begin inst32 = c_slli_2_slli;        end
		2'b01: begin inst32 = c_lwsp_2_lw;          end
		2'b10: begin
			if (inst16[12] == 1'b0) begin
			inst32 = (inst16[6:2] != 5'b0) ? c_mv_2_add : c_jr_2_jalr;
			end else begin
			if (inst16[6:2] != 5'b0) begin
				inst32 = c_add_2_add;
			end else begin
				inst32 = (inst16[11:7] == 5'b0) ? c_ebreak_2_ebreak : c_jalr_2_jalr;
			end
			end
		end 2'b11: begin inst32 = c_swsp_2_sw;      end
		endcase
	end 2'b11: begin illegal_instr = 1'b1; inst32 = 32'h13; end
	endcase
end

assign ack_o = ~illegal_instr;
assign inst32_o = ack_o ? inst32 : `INSTR_NOP;


/////////////////////////////////////
// 16-bit -> 32-bit Reconstruction //
/////////////////////////////////////

assign c_addi4spn_2_addi  = {2'b0, inst16[10:7], inst16[12:11], inst16[5], inst16[6], 2'b00, 5'h02, 3'b000, 2'b01, inst16[4:2], {OPCODE_OP_IMM}};
assign c_addi_2_addi      = {{6 {inst16[12]}}, inst16[12], inst16[6:2], inst16[11:7], 3'b0, inst16[11:7], {OPCODE_OP_IMM}};
assign c_addi16sp_2_addi  = {{3 {inst16[12]}}, inst16[4:3], inst16[5], inst16[2], inst16[6], 4'b0, 5'h02, 3'b000, 5'h02, {OPCODE_OP_IMM}};
assign c_li_2_addi        = {{6 {inst16[12]}}, inst16[12], inst16[6:2], 5'b0, 3'b0, inst16[11:7], {OPCODE_OP_IMM}};

assign c_lui_2_lui        = {{15 {inst16[12]}}, inst16[6:2], inst16[11:7], {OPCODE_LUI}};

assign c_add_2_add        = {7'b0, inst16[6:2], inst16[11:7], 3'b0, inst16[11:7], {OPCODE_OP}};
assign c_mv_2_add         = {7'b0, inst16[6:2], 5'b0, 3'b0, inst16[11:7], {OPCODE_OP}};

assign c_sub_2_sub        = {2'b01, 5'b0, 2'b01, inst16[4:2], 2'b01, inst16[9:7], 3'b000, 2'b01, inst16[9:7], {OPCODE_OP}};

assign c_lw_2_lw          = {5'b0, inst16[5], inst16[12:10], inst16[6], 2'b00, 2'b01, inst16[9:7], 3'b010, 2'b01, inst16[4:2], {OPCODE_LOAD}};
assign c_lwsp_2_lw        = {4'b0, inst16[3:2], inst16[12], inst16[6:4], 2'b00, 5'h02, 3'b010, inst16[11:7], OPCODE_LOAD};

assign c_sw_2_sw          = {5'b0, inst16[5], inst16[12], 2'b01, inst16[4:2], 2'b01, inst16[9:7], 3'b010, inst16[11:10], inst16[6], 2'b00, {OPCODE_STORE}};
assign c_swsp_2_sw        = {4'b0, inst16[8:7], inst16[12], inst16[6:2], 5'h02, 3'b010, inst16[11:9], 2'b00, {OPCODE_STORE}};

assign c_jal_2_jal        = {inst16[12], inst16[8], inst16[10:9], inst16[6], inst16[7], inst16[2], inst16[11], inst16[5:3], {9 {inst16[12]}}, 4'b0, ~inst16[15], {OPCODE_JAL}};

assign c_jr_2_jalr        = {12'b0, inst16[11:7], 3'b0, 5'b0, {OPCODE_JALR}};
assign c_jalr_2_jalr      = {12'b0, inst16[11:7], 3'b000, 5'b00001, {OPCODE_JALR}};

assign c_xor_2_xor        = {7'b0, 2'b01, inst16[4:2], 2'b01, inst16[9:7], 3'b100, 2'b01, inst16[9:7], {OPCODE_OP}};
assign c_or_2_or          = {7'b0, 2'b01, inst16[4:2], 2'b01, inst16[9:7], 3'b110, 2'b01, inst16[9:7], {OPCODE_OP}};
assign c_and_2_and        = {7'b0, 2'b01, inst16[4:2], 2'b01, inst16[9:7], 3'b111, 2'b01, inst16[9:7], {OPCODE_OP}};
assign c_andi_2_andi      = {{6 {inst16[12]}}, inst16[12], inst16[6:2], 2'b01, inst16[9:7], 3'b111, 2'b01, inst16[9:7], {OPCODE_OP_IMM}};
assign c_slli_2_slli      = {7'b0, inst16[6:2], inst16[11:7], 3'b001, inst16[11:7], {OPCODE_OP_IMM}};
assign c_srli_2_srli      = {1'b0, inst16[10], 5'b0, inst16[6:2], 2'b01, inst16[9:7], 3'b101, 2'b01, inst16[9:7], {OPCODE_OP_IMM}};

assign c_beqz_2_beq       = {{4 {inst16[12]}}, inst16[6:5], inst16[2], 5'b0, 2'b01, inst16[9:7], 2'b00, inst16[13], inst16[11:10], inst16[4:3], inst16[12], {OPCODE_BRANCH}};

assign c_ebreak_2_ebreak  = {32'h0010_0073};

/////////////////////////////////////



endmodule : cmp_decode
