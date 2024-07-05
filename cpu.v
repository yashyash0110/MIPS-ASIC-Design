module cpu(clk, rst, MEM_WRITE);

input clk,rst;
output wire[31:0] MEM_WRITE;
wire [31:0] nextPC, readPC, PCPlus4IF, PCPlus4ID, PCPlus4EX;
wire[31:0] branchAddress;
wire[31:0] instructionIF, instructionID;
wire[31:0] registerData1ID, registerData2ID, registerData1EX, registerData2EX;
wire[31:0] signExtendOutID, signExtendOutEX;
wire[31:0] shiftOut;
wire[3:0] ALUOpID, ALUOpEX;
wire[9:0] controlSignalsID;
wire[4:0] rsEX ,rtEX ,rdEX;
wire[31:0] ALUData1, ALUData2;
wire[31:0] ALUData2Mux_1Out;
wire[4:0] regDstMuxOut;
wire[31:0] ALU_OUT, ALUResultMEM, ALUResultWB;
wire[4:0] writeRegMEM, writeRegWB;
wire[1:0] upperMux_sel, lowerMux_sel;
wire[1:0] cmp_mux_sel_1,cmp_mux_sel_2;
wire[31:0] cmp_mux_out_1, cmp_mux_out_2;
wire[31:0] MEM_READ, MEM_WB_READ;
wire[31:0] regWriteDataMEM;
wire[3:0] ALUControl;
wire RegWriteWB;


PC PCRegister(nextPC ,rst , clk, holdPC,readPC);
InstructionMemory instructionMemory(clk, readPC, instructionIF);
Adder PCAdder(PCPlus4IF ,readPC, 32'h00000004);
Mux2x1_NBits #(32)nextPCMux(nextPC, PCPlus4IF, branchAddress, PCMuxSel);
and branchAndComparator(PCMuxSel, equalFlag, branchID);
IF_ID_reg IF_ID(clk, PCPlus4IF, instructionIF,holdIF_ID,PCMuxSel,instructionID, PCPlus4ID);


//ID_Stage
ControlUnit controlUnit(instructionID[31:26],rst,RegDstID,branchID,MemReadID,MemtoRegID,ALUOpID,MemWriteID,ALUSrcID,RegWriteID);
RegisterFile regiterFile(clk,rst,instructionID[25:21], instructionID[20:16], writeRegWB, regWriteDataMEM, RegWriteWB,  registerData1ID, registerData2ID);
Mux3x1_NBits #(32) comparatorMux1(cmp_mux_out_1, registerData1ID, ALUResultMEM, regWriteDataMEM, cmp_mux_sel_1);
Mux3x1_NBits #(32) comparatorMux2(cmp_mux_out_2, registerData2ID, ALUResultMEM, regWriteDataMEM, cmp_mux_sel_2);
Comparator comparator(cmp_mux_out_1, cmp_mux_out_2, equalFlag);
SignExtend signExtend(instructionID[15:0], signExtendOutID);
ShiftLeft2 shiftLeft2(shiftOut, signExtendOutID);
Adder branchAdder(branchAddress, shiftOut, PCPlus4ID);
HazardDetectionUnit hazardUnit(MemReadEX, MemReadMEM, rtEX, instructionID, holdPC, holdIF_ID, hazardMuxSelector);
Mux2x1_NBits #(10) ID_EXRegMux(controlSignalsID, {RegWriteID, MemtoRegID, MemWriteID, MemReadID, ALUSrcID, ALUOpID, RegDstID}
			,10'b0000000000, hazardMuxSelector);
ID_EX_reg ID_EX(clk,RegWriteID, MemtoRegID, MemWriteID, MemReadID, ALUSrcID, ALUOpID, RegDstID, PCPlus4ID,registerData1ID ,registerData2ID
		,signExtendOutID,instructionID[25:11],PCPlus4EX ,registerData1EX ,registerData2EX ,signExtendOutEX ,rsEX ,rtEX ,rdEX
		,RegWriteEX,MemtoRegEX,MemWriteEX, MemReadEX,ALUSrcEX, ALUOpEX, RegDstEX);


//EX_Stage
Mux3x1_NBits #(32) ALUData1Mux(ALUData1, registerData1EX, regWriteDataMEM, ALUResultMEM, upperMux_sel);
Mux3x1_NBits #(32) ALUData2Mux_1(ALUData2Mux_1Out, registerData2EX, regWriteDataMEM, ALUResultMEM, lowerMux_sel);
Mux2x1_NBits #(32) ALUData2Mux_2(ALUData2, ALUData2Mux_1Out, signExtendOutEX, ALUSrcEX);
ALUControl AluControl(ALUOpEX, signExtendOutEX[5:0],ALUControl);
ALU alu(clk,rst,ALUData1, ALUData2, ALUControl, signExtendOutEX[10:6], overFlow, zero, ALU_OUT);
Mux2x1_NBits #(5) regDstMux(regDstMuxOut, rtEX, rdEX, RegDstEX);
EX_Mem_reg EX_MEM(clk, RegWriteEX, MemtoRegEX, MemWriteEX, MemReadEX, ALU_OUT, ALUData2Mux_1Out
		,regDstMuxOut, RegWriteMEM, MemtoRegMEM, MemWriteMEM, MemReadMEM, ALUResultMEM, MEM_WRITE, writeRegMEM);
ForwardingUnit forwardingUnit(RegWriteMEM, writeRegMEM, RegWriteWB, writeRegWB, rsEX, rtEX
				,upperMux_sel,lowerMux_sel, cmp_mux_sel_1,cmp_mux_sel_2);


//MEM_Stage
DataMemory dataMemory(clk,MemWriteMEM, MemReadMEM, ALUResultMEM, MEM_WRITE,MEM_READ);
Mem_Wb_reg MEM_WB( clk,RegWriteMEM, MemtoRegMEM, ALUResultMEM, MEM_READ, writeRegMEM, RegWriteWB, MemtoRegWB,MEM_WB_READ
		,ALUResultWB, writeRegWB);


//WB_Stage
Mux2x1_NBits #(32) writeBackMux(regWriteDataMEM, ALUResultWB, MEM_WB_READ, MemtoRegWB);

endmodule


module Adder (o_res ,i_a, i_b);

input wire signed [31:0] i_a, i_b;
output wire [31:0] o_res;

assign o_res = i_a + i_b;

endmodule


module ALU(clk,rst,i_data1, i_data2, i_ALUControl, i_shiftAmount, o_overFlow, o_zero, o_ALUResult);

input wire rst,clk;
input wire signed [31:0] i_data1,i_data2;
input wire [3:0] i_ALUControl;
input wire [4:0] i_shiftAmount;
output  reg o_overFlow, o_zero;
output reg signed [31:0] o_ALUResult;


reg overFlow,zero;
reg signed [31:0] ALUResult;

always @(posedge clk)
begin
	o_overFlow <= overFlow;
	o_zero <= zero;
	o_ALUResult <= ALUResult;
end

wire [31:0] w_neg_data2;
assign w_neg_data2 = -i_data2;

parameter ADD = 4'b0000;
parameter SUB = 4'b0001;
parameter AND = 4'b0010;
parameter OR = 4'b0011;
parameter SHFT_L = 4'b0100;
parameter SHFT_R_L = 4'b0101;
parameter SHFT_R_A = 4'b0110;
parameter GREATER = 4'b0111;
parameter LESS = 4'b1000;
parameter NOR = 4'b1001;


always @(i_ALUControl, i_data1, i_data2,rst)
begin

if(rst)
zero = 1'b0;

else if(i_data1 == i_data2)
zero = 1'b1;

else
zero = 1'b0;

case(i_ALUControl)

ADD: 
	begin	
	
	ALUResult = i_data1 + i_data2;
	
	if(i_data1[31] == i_data2[31] && ALUResult[31] == ~i_data1[31])
	overFlow = 1'b1;
	
	else
	overFlow = 1'b0;
	
	end

SUB:
	begin
	
	ALUResult = i_data1 + w_neg_data2;
	
	if(i_data1[31] == w_neg_data2[31] && ALUResult[31] == ~i_data1[31])
	overFlow = 1'b1;
	
	else
	overFlow = 1'b0;
	
	end
	
AND:
	ALUResult = i_data1 & i_data2;

OR:
	ALUResult = i_data1 | i_data2;
	
SHFT_L:
	ALUResult = i_data1 << i_shiftAmount;

SHFT_R_L:
	ALUResult = i_data1 >> i_shiftAmount;

SHFT_R_A:
	ALUResult = i_data1 >>> i_shiftAmount;

GREATER:
	begin
	
	if(i_data1 > i_data2)
	ALUResult = 1;
	
	else
	ALUResult = 0;
	
	end

LESS:
	begin
	if(i_data1 < i_data2)
	ALUResult = 1;
	
	else
	ALUResult = 0;
	
	end

NOR:
	ALUResult = ~(i_data1 | i_data2);

endcase

end

endmodule


module ALUControl(i_ALUOp, i_funct, o_ALUControl);

input [3:0] i_ALUOp;
input [5:0] i_funct;
output [3:0] o_ALUControl;

assign o_ALUControl = 	((i_ALUOp == 4'b0000) ? 4'b0000:
								(i_ALUOp == 4'b0001) ? 4'b0001:
								(i_ALUOp == 4'b0011) ? 4'b0010:
								(i_ALUOp == 4'b0100) ? 4'b0011:
								(i_ALUOp == 4'b0101) ? 4'b1000:
								(i_ALUOp == 4'b0010) ? 
								
								((i_funct == 6'b100000) ? 4'b0000:
								(i_funct == 6'b100010) ? 4'b0001:
								(i_funct == 6'b100100) ? 4'b0010:
								(i_funct == 6'b100101) ? 4'b0011:
								(i_funct == 6'b100111) ? 4'b1001:
								(i_funct == 6'b101010) ? 4'b1000:
								(i_funct == 6'b000000) ? 4'b0100:
								(i_funct == 6'b000010) ? 4'b0101 : 4'bxxxx): 4'bxxxx);

endmodule


module Comparator(i_a ,i_b ,o_equal);

input [31:0]  i_a;
input [31:0]  i_b;
output o_equal;

assign o_equal = (i_a == i_b) ? 1'b1 : 1'b0;

endmodule

module ControlUnit (i_opcode,rst,o_RegDst,o_branch,o_Memread,o_MemtoReg,
							o_ALUop,o_MemWrite,o_AluSrc,o_RegWrite);
  
  input [5:0] i_opcode;
  input rst;
  output reg o_RegDst,o_branch,o_Memread,o_MemtoReg,o_MemWrite,o_AluSrc,o_RegWrite;
  output reg [3:0] o_ALUop;
  
  
  parameter R_type=6'b000000;
  parameter lw=6'b100011;
  parameter sw=6'b101011;
  parameter beq=6'b000100;
  parameter addi = 6'b001000; 
  parameter andi = 6'b001100; 
  parameter ori = 6'b001101;
  parameter slti = 6'b001010;

  always@(i_opcode,rst)
    begin
	 
		if(rst)
		begin
			o_RegDst = 1'b0;
			o_branch = 1'b0;
			o_Memread = 1'b0;
			o_MemtoReg = 1'b0;
			o_ALUop = 4'b0000;
			o_MemWrite = 1'b0;
			o_AluSrc = 1'b0;
			o_RegWrite = 1'b0;
		end
		
      case (i_opcode)

        R_type:           

          begin
          o_RegDst=1 ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=0 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0010 ;
          end
          
          
        
        lw:           

          begin
          o_RegDst=0 ;
          o_branch=0 ;
          o_Memread=1 ;
          o_MemtoReg=1 ;
          o_MemWrite=0 ;
          o_AluSrc=1 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0000 ;
          end
         
        
        sw:           

          begin
          //o_RegDst=1'bx ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=1 ;
          o_AluSrc=1 ;
          o_RegWrite=0 ;
          o_ALUop=4'b0000 ;
          end
          
        beq:           

          begin
          //o_RegDst=1'bx ;
          o_branch= 1;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=0 ;
          o_RegWrite=0 ;
          o_ALUop=4'b0001 ;
          end

	addi:           

          begin
          o_RegDst=0 ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=1 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0000 ;
          end

	andi:           

          begin
          o_RegDst=0 ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=1 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0011 ;
          end

	ori:           

          begin
          o_RegDst=0 ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=1 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0100 ;
          end

	slti:           

          begin
          o_RegDst=0 ;
          o_branch=0 ;
          o_Memread=0 ;
          o_MemtoReg=0 ;
          o_MemWrite=0 ;
          o_AluSrc=1 ;
          o_RegWrite=1 ;
          o_ALUop=4'b0101 ;
          end
			 
	default :
			 begin
			 o_RegDst = 1'b0;
			 o_branch = 1'b0;
			 o_Memread = 1'b0;
			 o_MemtoReg = 1'b0;
			 o_ALUop = 4'b0000;
			 o_MemWrite = 1'b0;
			 o_AluSrc = 1'b0;
			 o_RegWrite = 1'b0;
			 end
		
      endcase
      
    end
  
  
endmodule

module DataMemory (clk,i_MemWrite,i_Memread,i_address,i_writeData,o_readData);


input i_MemWrite,i_Memread,clk;
input [31:0] i_address,i_writeData;
output [31:0] o_readData;
  
reg [31:0] readData;
reg[31:0] memory [0:31];

assign o_readData = readData;
always@(negedge clk) // writing in the first half of the cycle.
begin
   if(i_MemWrite==1)
      memory[i_address]<=i_writeData;
end
  
always@(posedge clk)
begin
  if(i_Memread==1)
     readData <= memory[i_address];
end

endmodule

module EX_Mem_reg (clk,i_RegWrite, i_MemtoReg,i_MemWrite, 
						i_MemRead,i_ALUresult,i_writedata,i_writeReg,o_RegWriteOut, o_MemtoRegOut,o_MemWriteOut,
						o_MemReadOut,o_ALUresultOut,o_writedataOut,o_writeRegOut);
  
input clk;
input i_RegWrite, i_MemtoReg;
input i_MemWrite, i_MemRead; 
input [31:0] i_ALUresult,i_writedata;
input [4:0] i_writeReg;
output reg o_RegWriteOut, o_MemtoRegOut ,o_MemWriteOut, o_MemReadOut;
output reg [31:0] o_ALUresultOut,o_writedataOut;
output reg [4:0] o_writeRegOut;
  
always@(negedge clk)
begin
    o_RegWriteOut <= i_RegWrite;
    o_MemtoRegOut <= i_MemtoReg;
    o_MemWriteOut <= i_MemWrite;
    o_MemReadOut <= i_MemRead;
    o_ALUresultOut <= i_ALUresult;
    o_writedataOut <= i_writedata;
    o_writeRegOut <= i_writeReg;
      
end
  
endmodule


module ForwardingUnit(i_EX_MemRegwrite,i_EX_MemWriteReg,i_Mem_WbRegwrite,
							 i_Mem_WbWriteReg,i_ID_Ex_Rs,i_ID_Ex_Rt,
							 o_upperMux_sel,o_lowerMux_sel, o_cmp_mux_sel_1,o_cmp_mux_sel_2);
  
input i_EX_MemRegwrite, i_Mem_WbRegwrite;
input [4:0] i_EX_MemWriteReg , i_Mem_WbWriteReg, i_ID_Ex_Rs, i_ID_Ex_Rt;
output reg [1:0] o_upperMux_sel, o_lowerMux_sel;
output reg [1:0] o_cmp_mux_sel_1,o_cmp_mux_sel_2; 

always@(*)

begin
if(i_EX_MemRegwrite && i_EX_MemWriteReg)  //forwarding from ALU to ALU & from ALU to ID stage
begin
 if (i_EX_MemWriteReg==i_ID_Ex_Rs)
	begin
	
	o_upperMux_sel=2'b10;
	o_cmp_mux_sel_1=2'b01;
	end
 else //no forwarding
 begin
 o_upperMux_sel=2'b00;
 o_cmp_mux_sel_1=2'b00;
 end
	
 if(i_EX_MemWriteReg==i_ID_Ex_Rt)
	  begin
	o_lowerMux_sel=2'b10;
	o_cmp_mux_sel_2=2'b01;
	  end
 else //no forwarding
 begin
 o_lowerMux_sel=2'b00;
 o_cmp_mux_sel_2=2'b00;
 end
	
end

else if (i_Mem_WbRegwrite && i_Mem_WbWriteReg) //forwarding from Mem stage to ALU & from Mem stage to ID stage including double data hazard
begin
 if ((i_Mem_WbWriteReg==i_ID_Ex_Rs) && (i_EX_MemWriteReg!=i_ID_Ex_Rs))
	begin
	o_upperMux_sel=2'b01;
	o_cmp_mux_sel_1=2'b10;
	end
 else //no forwarding
 begin
 o_upperMux_sel=2'b00;
 o_cmp_mux_sel_1=2'b00;
 end
	

	
 if((i_Mem_WbWriteReg==i_ID_Ex_Rt) && (i_EX_MemWriteReg!=i_ID_Ex_Rt) )
 begin
	o_lowerMux_sel=2'b01;
	o_cmp_mux_sel_2=2'b10;
 end

 else //no forwarding
 begin
 o_lowerMux_sel=2'b00;
 o_cmp_mux_sel_2=2'b00;
 end
 
end

else    //No forwarding
begin
				 o_upperMux_sel=2'b00;
				 o_lowerMux_sel=2'b00;
				 o_cmp_mux_sel_1=2'b00;
				 o_cmp_mux_sel_2=2'b00;

 
end
end

endmodule

module HazardDetectionUnit(i_ID_ExMemRead,i_EX_MemMemRead,i_ID_Ex_Rt,i_IF_ID_Instr,
								o_no_change_pc,o_no_change_IF_ID,o_muxSelector);

input i_ID_ExMemRead,i_EX_MemMemRead;
input [4:0] i_ID_Ex_Rt;
input [31:0] i_IF_ID_Instr;
output reg o_no_change_pc, o_no_change_IF_ID, o_muxSelector;

parameter beqOPcode=6'b000100;

always@(*)
 begin
	if (i_ID_ExMemRead && (o_no_change_pc == 1'b0) && (o_no_change_IF_ID == 1'b0))
	  begin
		 if(i_ID_Ex_Rt==i_IF_ID_Instr[25:21] || i_ID_Ex_Rt==i_IF_ID_Instr[20:15] )
			begin
			  o_no_change_pc=1;
			  o_no_change_IF_ID=1;
			  o_muxSelector=1;
			end
	  end
	else if((i_IF_ID_Instr [31:26]==beqOPcode) && (o_no_change_pc == 1'b0) && (o_no_change_IF_ID == 1'b0))
	  begin
		 o_no_change_pc=1;
		 o_no_change_IF_ID=1;
		 o_muxSelector=1;
	  end
		 
	else
	  begin
		 o_no_change_pc=0;
		 o_no_change_IF_ID=0;
		 o_muxSelector=0;     
	  end    
	
 end


endmodule


module ID_EX_reg (clk,i_RegWrite, i_MemtoReg, i_MemWrite, i_MemRead,i_ALUSrc, i_ALUOp, 
					i_RegDst, i_PCplus4 ,i_ReadData1_in ,i_ReadData2_in,i_SignExtendResult_in,
					i_regAddresss_in ,o_PCplus4out ,o_ReadData1_out ,o_ReadData2_out ,i_SignExtendResult_out, 
					o_rsOut ,o_rtOut ,o_rdOut, o_RegWriteOut,o_MemtoRegOut,o_MemWriteOut, 
					o_MemReadOut,o_ALUSrcOut, o_ALUOpOut, o_RegDstOut);

input wire i_RegWrite, i_MemtoReg;
input wire i_MemWrite, i_MemRead; 
input wire i_ALUSrc, i_RegDst;
input wire [3:0] i_ALUOp;
input wire [31:0] i_PCplus4 ,i_ReadData1_in ,i_ReadData2_in ,i_SignExtendResult_in;
input wire [14:0] i_regAddresss_in;
input wire clk;



output reg o_RegWriteOut, o_MemtoRegOut;
output reg o_MemWriteOut, o_MemReadOut;
output reg o_ALUSrcOut, o_RegDstOut;
output reg [3:0] o_ALUOpOut;
output reg [31:0] o_PCplus4out ,o_ReadData1_out ,o_ReadData2_out ,i_SignExtendResult_out;
output reg [4:0] o_rsOut ,o_rtOut ,o_rdOut;


always @(negedge clk)
 begin
	o_PCplus4out <= i_PCplus4;
	o_ReadData1_out <= i_ReadData1_in;
	o_ReadData2_out <= i_ReadData2_in;
	i_SignExtendResult_out <= i_SignExtendResult_in;
	o_rsOut <= i_regAddresss_in[14:10];
	o_rtOut <= i_regAddresss_in[9:5];
	o_rdOut <= i_regAddresss_in[4:0];
	o_RegWriteOut <= i_RegWrite;
	o_MemtoRegOut <= i_MemtoReg;
	o_MemWriteOut <= i_MemWrite;
	o_MemReadOut <= i_MemRead;
	o_ALUSrcOut <= i_ALUSrc;
	o_ALUOpOut <= i_ALUOp;
	o_RegDstOut <= i_RegDst;
 end

endmodule



module IF_ID_reg(clk, i_PCplus4, i_instrIn, i_no_change, i_IF_flush, o_instrOut, o_PCplus4Out);

input wire [31:0] i_instrIn,i_PCplus4;
input clk ,i_no_change,i_IF_flush;
output reg [31:0] o_instrOut, o_PCplus4Out;

always @(negedge clk)
 begin
	
	if (i_no_change==1'b0) 
	begin	
	
	o_PCplus4Out <= i_PCplus4;	 
	o_instrOut  <= i_instrIn;
		 
	end
	
	else if (i_IF_flush==1'b1)
	begin
	
	o_PCplus4Out <= i_PCplus4; 
	o_instrOut <= 32'b0;
	
	end
	
	
 end

endmodule

module InstructionMemory(clk,i_pc,o_readdata);

input clk;
input  [31:0] i_pc;

reg [31:0] Imemory [0:1023];

output reg [31:0] o_readdata;

//initial 
//begin
//		$readmemh("TEST1.txt",Imemory);
//end


always @ (posedge clk)
begin	 
	o_readdata <= Imemory[i_pc>>2]; // 32 bit addressable ,memory
end			
		
endmodule	

module Mem_Wb_reg(clk,i_RegWrite, i_MemtoReg,i_ALUresult,
					i_readData,i_writeReg,o_RegWriteOut,o_MemtoRegOut,o_i_readDataOut,o_ALUresultOut,o_ALUresult);

input clk;
input i_RegWrite, i_MemtoReg;
input [4:0] i_writeReg;
input [31:0] i_ALUresult, i_readData;
output reg o_RegWriteOut, o_MemtoRegOut;
output reg [31:0] o_i_readDataOut,o_ALUresultOut;
output reg [4:0] o_ALUresult;

always@(negedge clk)
begin
	o_RegWriteOut <= i_RegWrite;
	o_MemtoRegOut <= i_MemtoReg;
	o_i_readDataOut <= i_readData;
	o_ALUresultOut <= i_ALUresult;
	o_ALUresult <= i_writeReg;
	
end


endmodule

module Mux2x1_NBits(out, in1, in2, i_sel);

parameter LEN = 5; 

input [LEN-1:0] in1, in2;
input i_sel;

output [LEN-1:0] out;

assign out = 	(i_sel == 1'b0) ? in1 :  in2 ;

endmodule

module Mux3x1_NBits(out, in1, in2, in3, i_sel);

parameter LEN = 32;

input [LEN-1:0] in1, in2, in3;
input [1:0] i_sel;

output [LEN-1:0]out;

assign out = (i_sel == 2'b00) ? in1 : (i_sel == 2'b01) ? in2 : (i_sel == 2'b10) ? in3 : 32'd0;

endmodule


module PC (i_nextPC ,rst ,clk, i_no_change_pc, o_outPC);

input wire [31:0] i_nextPC;
input rst , clk, i_no_change_pc;

output reg [31:0] o_outPC;



always @(posedge clk)
begin

  if (rst)
		begin
			o_outPC <= 32'hFFFFFFFC; // +0x4 will result into 0x0.
		end
		
  else if (i_no_change_pc==0) 
	  begin
			o_outPC <= i_nextPC;
	  end
	  
  else
	  begin
			o_outPC <= o_outPC;
	  end
	
end

endmodule

module RegisterFile(clk,rst, i_ReadReg1, i_ReadReg2, i_WriteReg, i_WriteData, i_RegWrite, 
							o_ReadData1, o_ReadData2 );


input [4:0] i_ReadReg1 ,i_ReadReg2 ,i_WriteReg;
input [31:0] i_WriteData;
input i_RegWrite ,clk, rst;


output reg [31:0] o_ReadData1 ,o_ReadData2;

integer k;

reg [31:0] memory[0:31];

always @(posedge clk)

begin

	o_ReadData1 <= memory[i_ReadReg1];
	o_ReadData2 <= memory[i_ReadReg2];

end

always @(negedge clk)
begin

	if(rst)
	begin
		for(k=0;k<32;k=k+1)
		begin
			memory[k] = k;
		end
	end
	
	else if (i_RegWrite == 1)
	begin
		 memory[i_WriteReg] <= i_WriteData;
	end
end

endmodule

module ShiftLeft2(out, in);

input [31:0]in;
output [31:0]out;

assign out = in << 2;

endmodule

module SignExtend(in ,out);

input  [15:0] in;
output [31:0] out;

assign out =  (in[15] == 1)? {16'hffff , in} : {16'h0000 ,in} ;

endmodule
