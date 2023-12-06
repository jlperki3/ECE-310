module half_adder(sum, carry, a, b);
  input a, b;
  output sum, carry;
  xor sum1(sum, a, b);
  and carry1(carry, a, b);
endmodule

module full_adder_1bit(fsum, fcarry_out, a, b, c);
  input a, b, c;
  output fcarry_out;
  output fsum;
  wire half_sum_1, half_carry_1, half_carry_2;
  half_adder HA1(half_sum_1, half_carry_1, a, b); //instance 1 of Half Adder
  half_adder HA2(fsum, half_carry_2, half_sum_1, c); //instance 2 of Half Adder
  or or1(fcarry_out, half_carry_2, half_carry_1);
endmodule

module full_adder_4bit(fsum, fcarry_out, a, b, cin);
  input [3:0]a, b;
  input cin;
  output [3:0]fsum;
  output fcarry_out;
  wire cb0, cb1, cb2;
  full_adder_1bit B3(fsum[3], fcarry_out, a[3], b[3], cb2);
  full_adder_1bit B2(fsum[2], cb2, a[2], b[2], cb1);
  full_adder_1bit B1(fsum[1], cb1, a[1], b[1], cb0);
  full_adder_1bit B0(fsum[0], cb0, a[0], b[0], cin);
endmodule

module full_lookaheadadder_4bit(fsum, fcarry_out, a, b, cin);
  input [3:0]a, b;
  input cin;
  output reg [3:0]fsum;
  output reg fcarry_out;
  reg [3:0]p, g;
  reg [4:0] c;
  always @(*) begin
    p = a ^ b;
    g = a & b;
    c[0] = cin;
    c[1] = g[0] | (p[0] & c[0]);
    c[2] = g[1] | (p[1] & g[0]) | (p[1] & p[0] & c[0]);
    c[3] = g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]) | (p[2] & p[1] & p[0] & c[0]);
    c[4] = g[3] | (p[3] & g[2]) | (p[3] & p[2] & g[1]) | (p[3] & p[2] & p[1] & g[0]) | (p[3] & p[2] & p[1] & p[0] & c[0]);
    fsum = p ^ c[3:0];
    fcarry_out = c[4];
  end
endmodule

module full_adder_8bit(fsum, fcarry_out, a, b, cin);
  input [7:0] a,b;
  input cin;
  output [7:0] fsum;
  output fcarry_out;
  wire carry_mid;
  //full_adder_4bit fsum74(fsum[7:4],fcarry_out, a[7:4], b[7:4], carry_mid);
  //full_adder_4bit fsum30(fsum[3:0], carry_mid, a[3:0], b[3:0], cin);
  full_lookaheadadder_4bit fsum74(fsum[7:4],fcarry_out, a[7:4], b[7:4], carry_mid);
  full_lookaheadadder_4bit fsum30(fsum[3:0], carry_mid, a[3:0], b[3:0], cin);
endmodule

module full_adder_16bit(fsum, fcarry_out, a, b, cin);
  input [15:0] a,b;
  input cin;
  output [15:0] fsum;
  output fcarry_out;
  wire carry_mid;
  full_adder_8bit fsum8_1(fsum[15:8],fcarry_out, a[15:8], b[15:8], carry_mid);
  full_adder_8bit fsum8_0(fsum[7:0], carry_mid, a[7:0], b[7:0], cin);
endmodule

module mux_2 (out, i0, i1, sel);
  input i0, i1, sel;
  output out;
  wire n_sel, x1, x2;
  or (out, x1, x2);
  and (x1, i0, n_sel);
  and (x2, i1, sel);
  not (n_sel, sel);
endmodule

module mux_4bit( Out, A, B, sel);
  input [3:0] A,B;
  input sel;
  output [3:0]Out;
  // no internal nets or registers
  mux_2 m3 (Out[3], A[3], B[3], sel);
  mux_2 m2 (Out[2], A[2], B[2], sel);
  mux_2 m1 (Out[1], A[1], B[1], sel);
  mux_2 m0 (Out[0], A[0], B[0], sel);
endmodule

module mux_8bit ( Out, A, B, sel);
  input [7:0] A,B;
  input sel;
  output [7:0]Out;
  // no internal nets or registers
  mux_4bit m1_4 (Out[7:4], A[7:4], B[7:4], sel);
  mux_4bit m0_4 (Out[3:0], A[3:0], B[3:0], sel);
endmodule

module mymul_8bitgate(mout, a, b);
  input [3:0] a,b;
  output [7:0] mout;
  wire [3:0] m0_out, m1_out, m2_out, m3_out;
  wire [7:0]fsum_p0, fsum_p1, fsum_p2;
  wire fcarryout_p0, fcarryout_p1, fcarryout_p2, fcarryout_p3;
  mux_4bit m0(m0_out, {4{1'b0}}, a, b[0]);
  mux_4bit m1(m1_out, {4{1'b0}}, a, b[1]);
  mux_4bit m2(m2_out, {4{1'b0}}, a, b[2]);
  mux_4bit m3(m3_out, {4{1'b0}}, a, b[3]);
  full_adder_8bit a0 (fsum_p0, fcarryout_p0, {8{1'b0}}, {{4{1'b0}}, m0_out}, 1'b0);
  full_adder_8bit a1 (fsum_p1, fcarryout_p1, fsum_p0, {{3{1'b0}}, m1_out, {1{1'b0}}}, fcarryout_p0);
  full_adder_8bit a2 (fsum_p2, fcarryout_p2, fsum_p1, {{2{1'b0}}, m2_out, {2{1'b0}}}, fcarryout_p1);
  full_adder_8bit a3 (mout, fcarryout_p3, fsum_p2, {{1{1'b0}}, m3_out, {3{1'b0}}}, fcarryout_p2);
endmodule

module mymul_16bitgate(mout, a, b);
  input [7:0] a,b;
  output [15:0] mout;
  wire [7:0] m0_out, m1_out, m2_out, m3_out, m4_out, m5_out, m6_out, m7_out;
  wire [15:0]fsum_p0, fsum_p1, fsum_p2, fsum_p3, fsum_p4, fsum_p5, fsum_p6, fsum_p7;
  wire fcarryout_p0, fcarryout_p1, fcarryout_p2, fcarryout_p3, fcarryout_p4, fcarryout_p5, fcarryout_p6;
  mux_8bit m0(m0_out, {8{1'b0}}, a, b[0]);
  mux_8bit m1(m1_out, {8{1'b0}}, a, b[1]);
  mux_8bit m2(m2_out, {8{1'b0}}, a, b[2]);
  mux_8bit m3(m3_out, {8{1'b0}}, a, b[3]);
  mux_8bit m4(m4_out, {8{1'b0}}, a, b[4]);
  mux_8bit m5(m5_out, {8{1'b0}}, a, b[5]);
  mux_8bit m6(m6_out, {8{1'b0}}, a, b[6]);
  mux_8bit m7(m7_out, {8{1'b0}}, a, b[7]);
  full_adder_16bit a0 (fsum_p0, fcarryout_p0, {16{1'b0}}, {{8{1'b0}}, m0_out}, 1'b0);
  full_adder_16bit a1 (fsum_p1, fcarryout_p1, fsum_p0, {{7{1'b0}}, m1_out, {1{1'b0}}}, fcarryout_p0);
  full_adder_16bit a2 (fsum_p2, fcarryout_p2, fsum_p1, {{6{1'b0}}, m2_out, {2{1'b0}}}, fcarryout_p1);
  full_adder_16bit a3 (fsum_p3, fcarryout_p3, fsum_p2, {{5{1'b0}}, m3_out, {3{1'b0}}}, fcarryout_p2);
  full_adder_16bit a4 (fsum_p4, fcarryout_p4, fsum_p3, {{4{1'b0}}, m4_out, {4{1'b0}}}, fcarryout_p3);
  full_adder_16bit a5 (fsum_p5, fcarryout_p5, fsum_p4, {{3{1'b0}}, m5_out, {5{1'b0}}}, fcarryout_p4);
  full_adder_16bit a6 (fsum_p6, fcarryout_p6, fsum_p5, {{2{1'b0}}, m6_out, {6{1'b0}}}, fcarryout_p5);
  full_adder_16bit a7 (mout, fcarryout_p7, fsum_p6, {{1{1'b0}}, m7_out, {7{1'b0}}}, fcarryout_p6);
endmodule

module mymul_8bitgate_twocomp(mout, a, b);
  input [3:0] a,b;
  output reg [7:0] mout;
  wire [15:0] mout_16;
  always @(*) begin
    mout = mout_16[7:0];
  end
  mymul_16bitgate mul0 (mout_16, {{4{a[3]}},a}, {{4{b[3]}},b});
endmodule

module proj1(clk, rst, MemRW_IO, MemAddr_IO, MemD_IO);
  input clk;
  input rst;
  output MemRW_IO;
  output [7:0] MemAddr_IO;
  output [15:0] MemD_IO;
  
  wire zflag, muxPC, muxMAR, muxACC, loadMAR, loadPC, loadACC, loadMDR, loadIR, MemRW;
  wire [2:0] opALU;
  wire [7:0] MemAddr, opcode;
  wire [15:0] MemD, MemQ;
  //one instance of memory
  ram RAM1 (MemRW, MemD, MemQ, MemAddr);
  
  //one instance of controller
  ctr CTR1 (clk, rst, zflag, opcode, muxPC, muxMAR, muxACC, loadMAR, loadPC, loadACC, loadMDR, loadIR, opALU, MemRW);
    
  //one instance of datapath1
  datapath D1 (clk, rst, muxPC, muxMAR, muxACC, loadMAR, loadPC, loadACC, loadMDR, loadIR, opALU, zflag, opcode, MemAddr, MemD, MemQ);
  
  //these are just to observe the signals.
  assign MemRW_IO = MemRW;
  assign MemAddr_IO = MemAddr;
  assign MemD_IO = MemD;
endmodule

module ram(we, d, q, addr);
  input we;
  input [15:0] d;
  output reg [15:0] q;
  input [7:0] addr;
  
  reg [15:0] MEM [0:255];
  
  always @ (*) begin
    if (we) 
      MEM[addr] <= d;
    else    
      q <= MEM[addr];
  end    
endmodule

module alu(A, B, opALU, Rout);
  input [15:0] A, B;
  input [2:0] opALU;
  output reg [15:0] Rout;
  
  wire Cout;
  wire [15:0] AddOut, SubOut;
  wire [15:0] MulOut;
  
  full_adder_16bit ADD1 (AddOut, Cout, A, B, 1'b0);
  full_adder_16bit SUB1(SubOut, Cout, A, ~B, 1'b1);
  mymul_16bitgate MUL1 (MulOut, A[7:0], B[7:0]);  
  
  always @(*) begin 
    if      (opALU == 1) Rout = AddOut;
    else if (opALU == 2) Rout = SubOut;
    else if (opALU == 3) Rout = MulOut;
    else if (opALU == 4) Rout = A / B;
    else if (opALU == 5) Rout = A ^ B;
  end
endmodule

module ctr (clk, rst, zflag, opcode, muxPC, muxMAR, muxACC, loadMAR, loadPC, loadACC, loadMDR, loadIR, opALU, MemRW);
  input clk;
  input rst;
  input zflag;
  input [7:0]opcode;
  output reg muxPC;
  output reg muxMAR;
  output reg muxACC;
  output reg loadMAR;
  output reg loadPC;
  output reg loadACC;
  output reg loadMDR;
  output reg loadIR;
  output reg [2:0] opALU;
  output reg MemRW;
  
  reg [4:0] cstate, nstate;
  
  
  parameter fetch_1 = 5'b00000, fetch_2 = 5'b00001, fetch_3 = 5'b00010, decode = 5'b00011, add_1 = 5'b00100, add_2 = 5'b00101,
  sub_1 = 5'b00110, sub_2 = 5'b00111, mul_1 = 5'b01000, mul_2 = 5'b01001, div_1 = 5'b01010, div_2 = 5'b01011, xor_1 = 5'b01100, 
  xor_2 = 5'b01101, jump = 5'b01110, jumpz = 5'b01111, store = 5'b10000, load_1 = 5'b10001, load_2 = 5'b10010;
  

  always @ (posedge clk) begin 
    if (rst) begin
      cstate = fetch_1;
    end
    else begin
      cstate = nstate;
    end
  end 
    
  always @ (*) begin    
    case (cstate)
      fetch_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b1; 
        loadPC = 1'b1; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = fetch_2;
      end
      fetch_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = fetch_3;
      end
      fetch_3: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b1; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = decode;
      end
      decode: begin
        muxPC = 1'b0; 
        muxMAR = 1'b1; 
        muxACC = 1'b0; 
        loadMAR = 1'b1; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
      if      (opcode == 1) nstate = add_1;
      else if (opcode == 2) nstate = sub_1;
      else if (opcode == 3) nstate = mul_1;
      else if (opcode == 4) nstate = div_1;
      else if (opcode == 5) nstate = xor_1;
      else if ((opcode == 6) || (opcode == 7 && zflag == 1)) nstate = jump;
      else if (opcode == 7 && zflag == 0) nstate = jumpz;
      else if (opcode == 8) nstate = store;
      else if (opcode == 9) nstate = load_1;
      end
      add_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate  = add_2;
      end
      add_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b001; 
        MemRW = 1'b0;
        nstate = fetch_1;
      end
      sub_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = sub_2;
      end
      sub_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b010; 
        MemRW = 1'b0;
        nstate = fetch_1;
      end
      mul_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate  = mul_2;
      end
      mul_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b011; 
        MemRW = 1'b0;
        nstate  = fetch_1;
      end
      div_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = div_2;
      end
      div_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b100; 
        MemRW = 1'b0;
        nstate = fetch_1;
      end
      xor_1: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = xor_2;
      end
      xor_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b101; 
        MemRW = 1'b0;
        nstate = fetch_1;
      end
      
      jump: begin
        muxPC = 1'b1; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b1; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate = fetch_2;
      end
      jumpz: begin
        nstate  = fetch_1;
      end
      store: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b1;
        nstate = fetch_1;
      end
      load_1: begin 
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b0; 
        loadMDR = 1'b1; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate  = load_2;
      end
      load_2: begin
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b1; 
        loadMAR = 1'b0; 
        loadPC = 1'b0; 
        loadACC = 1'b1; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
        nstate  = fetch_1;
      end
      
      default: begin
        nstate = fetch_1;
        muxPC = 1'b0; 
        muxMAR = 1'b0; 
        muxACC = 1'b0; 
        loadMAR = 1'b1; 
        loadPC = 1'b1; 
        loadACC = 1'b0; 
        loadMDR = 1'b0; 
        loadIR = 1'b0; 
        opALU = 3'b000; 
        MemRW = 1'b0;
      end
    endcase
  end
endmodule
 
module registers(clk, rst, PC_reg, PC_next, IR_reg, IR_next, ACC_reg, ACC_next, MDR_reg, MDR_next, MAR_reg, MAR_next, zflag_reg, zflag_next);
  input wire clk;
  input wire rst;
  output reg [7:0]PC_reg;
  input wire [7:0]PC_next;
  output reg [15:0]IR_reg;
  input wire [15:0]IR_next;
  output reg [15:0]ACC_reg;
  input wire [15:0]ACC_next;
  output reg [15:0]MDR_reg;
  input wire [15:0]MDR_next;
  output reg [7:0]MAR_reg;
  input wire [7:0]MAR_next;
  output reg zflag_reg;
  input wire zflag_next;
  
  always @(posedge clk) begin
    if (rst) begin
      PC_reg <= 0;
      IR_reg <= 0;
      ACC_reg <= 0;
      MDR_reg <= 0;
      MAR_reg <= 0;
      zflag_reg <= 0;
    end
    else begin
      PC_reg <= PC_next;
      IR_reg <= IR_next;
      ACC_reg <= ACC_next;
      MDR_reg <= MDR_next;
      MAR_reg <= MAR_next;
      zflag_reg <= zflag_next;
    end
  end
endmodule

module datapath(clk, rst, muxPC, muxMAR, muxACC, loadMAR, loadPC, loadACC, loadMDR, loadIR, opALU, zflag, opcode, MemAddr, MemD, MemQ);
  input clk;
  input rst;
  input muxPC;
  input muxMAR;
  input muxACC;
  input loadMAR;
  input loadPC;
  input loadACC;
  input loadMDR;
  input loadIR;
  input [2:0] opALU;
  output zflag;
  output [7:0]opcode;
  output [7:0]MemAddr;
  output [15:0]MemD;
  input [15:0]MemQ;
  reg [7:0]PC_next;
  wire [15:0]IR_next;
  reg [15:0]ACC_next;
  wire [15:0]MDR_next;
  reg [7:0]MAR_next;
  reg zflag_next;
  wire [7:0]PC_reg;
  wire [15:0]IR_reg;
  wire [15:0]ACC_reg;
  wire [15:0]MDR_reg;
  wire [7:0]MAR_reg;
  wire zflag_reg;
  wire [15:0]ALU_out;
 //fill in the code here from page 8 of the document
 
  alu ALU1 (ACC_reg, MDR_reg, opALU, ALU_out);
  
  registers REGS1 (clk, rst, PC_reg, PC_next, IR_reg, IR_next, ACC_reg, ACC_next, MDR_reg, MDR_next, MAR_reg, MAR_next, zflag_reg, zflag_next);
  
  always @ (*) begin
    if (loadPC)  
      PC_next = muxPC?IR_reg[15:8]:(PC_reg+1'b1);
    else 
      PC_next = PC_reg;
      
    if (loadACC)
      ACC_next = muxACC?MDR_reg:ALU_out;
    else 
      ACC_next = ACC_reg;

    if (loadMAR)
      MAR_next = muxMAR?IR_reg[15:8]:PC_reg;
    else
      MAR_next = MAR_reg;
      
    zflag_next = (ACC_reg == 0);
    
  end
  
  assign IR_next   = loadIR?MDR_reg:IR_reg;
  assign MDR_next  = loadMDR?MemQ:MDR_reg;
  assign zflag     = (ACC_reg==0);
  assign opcode    = IR_reg[7:0];
  assign MemAddr   = MAR_reg;
  assign MemD      = ACC_reg;
  
endmodule


module proj1_tb();
  reg clk, rst;
  wire MemRW_IO;
  wire [7:0] MemAddr_IO;
  wire [15:0] MemD_IO;
 
  proj1 dut(clk, rst, MemRW_IO, MemAddr_IO, MemD_IO);

  always
    #5 clk = !clk;

  initial begin
    clk=1'b0;
    rst=1'b1;
    $readmemh("memory.list", proj1_tb.dut.RAM1.MEM);
    #20 rst=1'b0;
    #1700 //might need to be very large
    $display("Final value\n");
    $display("0x0010 %d\n",proj1_tb.dut.RAM1.MEM[16'h0010]);
    #4000 $stop;
  end
endmodule