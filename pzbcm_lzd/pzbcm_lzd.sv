//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_lzd #(
  parameter int WIDTH     = 8,
  parameter bit FROM_MSB  = 1
);
  localparam  int MAX_WIDTH   = 512;
  localparam  int NIBBLES     = (WIDTH + 3) / 4;
  localparam  int MAX_NIBBLES = MAX_WIDTH / 4;
  localparam  int COUNT_WIDTH = $clog2(WIDTH + 1);

  initial begin
    assume (WIDTH inside {[1:MAX_WIDTH]});
  end

  typedef logic [NIBBLES-1:0][3:0]  pzbcm_lzd_nibbles;

  function automatic logic [COUNT_WIDTH-1:0] get_leading_zero_count(
    logic [WIDTH-1:0] bits
  );
    pzbcm_lzd_nibbles             nibbles;
    logic [MAX_NIBBLES-1:0]       all_zero;
    logic [MAX_NIBBLES-1:0][1:0]  local_count;

    if (FROM_MSB) begin
      nibbles = pzbcm_lzd_nibbles'({<<{bits}});
    end
    else begin
      nibbles = pzbcm_lzd_nibbles'(bits);
    end

    all_zero    = '1;
    local_count = '0;
    for (int i = 0;i < NIBBLES;++i) begin
      {all_zero[i], local_count[i]} = __calc_nlc(nibbles[i]);
    end

    case (all_zero) inside
      {{128{1'b1}}                   }: return COUNT_WIDTH'(WIDTH);
      {{127{1'b?}}, 1'b0             }: return COUNT_WIDTH'({7'(  0), local_count[  0]});
      {{126{1'b?}}, 1'b0, {  1{1'b1}}}: return COUNT_WIDTH'({7'(  1), local_count[  1]});
      {{125{1'b?}}, 1'b0, {  2{1'b1}}}: return COUNT_WIDTH'({7'(  2), local_count[  2]});
      {{124{1'b?}}, 1'b0, {  3{1'b1}}}: return COUNT_WIDTH'({7'(  3), local_count[  3]});
      {{123{1'b?}}, 1'b0, {  4{1'b1}}}: return COUNT_WIDTH'({7'(  4), local_count[  4]});
      {{122{1'b?}}, 1'b0, {  5{1'b1}}}: return COUNT_WIDTH'({7'(  5), local_count[  5]});
      {{121{1'b?}}, 1'b0, {  6{1'b1}}}: return COUNT_WIDTH'({7'(  6), local_count[  6]});
      {{120{1'b?}}, 1'b0, {  7{1'b1}}}: return COUNT_WIDTH'({7'(  7), local_count[  7]});
      {{119{1'b?}}, 1'b0, {  8{1'b1}}}: return COUNT_WIDTH'({7'(  8), local_count[  8]});
      {{118{1'b?}}, 1'b0, {  9{1'b1}}}: return COUNT_WIDTH'({7'(  9), local_count[  9]});
      {{117{1'b?}}, 1'b0, { 10{1'b1}}}: return COUNT_WIDTH'({7'( 10), local_count[ 10]});
      {{116{1'b?}}, 1'b0, { 11{1'b1}}}: return COUNT_WIDTH'({7'( 11), local_count[ 11]});
      {{115{1'b?}}, 1'b0, { 12{1'b1}}}: return COUNT_WIDTH'({7'( 12), local_count[ 12]});
      {{114{1'b?}}, 1'b0, { 13{1'b1}}}: return COUNT_WIDTH'({7'( 13), local_count[ 13]});
      {{113{1'b?}}, 1'b0, { 14{1'b1}}}: return COUNT_WIDTH'({7'( 14), local_count[ 14]});
      {{112{1'b?}}, 1'b0, { 15{1'b1}}}: return COUNT_WIDTH'({7'( 15), local_count[ 15]});
      {{111{1'b?}}, 1'b0, { 16{1'b1}}}: return COUNT_WIDTH'({7'( 16), local_count[ 16]});
      {{110{1'b?}}, 1'b0, { 17{1'b1}}}: return COUNT_WIDTH'({7'( 17), local_count[ 17]});
      {{109{1'b?}}, 1'b0, { 18{1'b1}}}: return COUNT_WIDTH'({7'( 18), local_count[ 18]});
      {{108{1'b?}}, 1'b0, { 19{1'b1}}}: return COUNT_WIDTH'({7'( 19), local_count[ 19]});
      {{107{1'b?}}, 1'b0, { 20{1'b1}}}: return COUNT_WIDTH'({7'( 20), local_count[ 20]});
      {{106{1'b?}}, 1'b0, { 21{1'b1}}}: return COUNT_WIDTH'({7'( 21), local_count[ 21]});
      {{105{1'b?}}, 1'b0, { 22{1'b1}}}: return COUNT_WIDTH'({7'( 22), local_count[ 22]});
      {{104{1'b?}}, 1'b0, { 23{1'b1}}}: return COUNT_WIDTH'({7'( 23), local_count[ 23]});
      {{103{1'b?}}, 1'b0, { 24{1'b1}}}: return COUNT_WIDTH'({7'( 24), local_count[ 24]});
      {{102{1'b?}}, 1'b0, { 25{1'b1}}}: return COUNT_WIDTH'({7'( 25), local_count[ 25]});
      {{101{1'b?}}, 1'b0, { 26{1'b1}}}: return COUNT_WIDTH'({7'( 26), local_count[ 26]});
      {{100{1'b?}}, 1'b0, { 27{1'b1}}}: return COUNT_WIDTH'({7'( 27), local_count[ 27]});
      {{ 99{1'b?}}, 1'b0, { 28{1'b1}}}: return COUNT_WIDTH'({7'( 28), local_count[ 28]});
      {{ 98{1'b?}}, 1'b0, { 29{1'b1}}}: return COUNT_WIDTH'({7'( 29), local_count[ 29]});
      {{ 97{1'b?}}, 1'b0, { 30{1'b1}}}: return COUNT_WIDTH'({7'( 30), local_count[ 30]});
      {{ 96{1'b?}}, 1'b0, { 31{1'b1}}}: return COUNT_WIDTH'({7'( 31), local_count[ 31]});
      {{ 95{1'b?}}, 1'b0, { 32{1'b1}}}: return COUNT_WIDTH'({7'( 32), local_count[ 32]});
      {{ 94{1'b?}}, 1'b0, { 33{1'b1}}}: return COUNT_WIDTH'({7'( 33), local_count[ 33]});
      {{ 93{1'b?}}, 1'b0, { 34{1'b1}}}: return COUNT_WIDTH'({7'( 34), local_count[ 34]});
      {{ 92{1'b?}}, 1'b0, { 35{1'b1}}}: return COUNT_WIDTH'({7'( 35), local_count[ 35]});
      {{ 91{1'b?}}, 1'b0, { 36{1'b1}}}: return COUNT_WIDTH'({7'( 36), local_count[ 36]});
      {{ 90{1'b?}}, 1'b0, { 37{1'b1}}}: return COUNT_WIDTH'({7'( 37), local_count[ 37]});
      {{ 89{1'b?}}, 1'b0, { 38{1'b1}}}: return COUNT_WIDTH'({7'( 38), local_count[ 38]});
      {{ 88{1'b?}}, 1'b0, { 39{1'b1}}}: return COUNT_WIDTH'({7'( 39), local_count[ 39]});
      {{ 87{1'b?}}, 1'b0, { 40{1'b1}}}: return COUNT_WIDTH'({7'( 40), local_count[ 40]});
      {{ 86{1'b?}}, 1'b0, { 41{1'b1}}}: return COUNT_WIDTH'({7'( 41), local_count[ 41]});
      {{ 85{1'b?}}, 1'b0, { 42{1'b1}}}: return COUNT_WIDTH'({7'( 42), local_count[ 42]});
      {{ 84{1'b?}}, 1'b0, { 43{1'b1}}}: return COUNT_WIDTH'({7'( 43), local_count[ 43]});
      {{ 83{1'b?}}, 1'b0, { 44{1'b1}}}: return COUNT_WIDTH'({7'( 44), local_count[ 44]});
      {{ 82{1'b?}}, 1'b0, { 45{1'b1}}}: return COUNT_WIDTH'({7'( 45), local_count[ 45]});
      {{ 81{1'b?}}, 1'b0, { 46{1'b1}}}: return COUNT_WIDTH'({7'( 46), local_count[ 46]});
      {{ 80{1'b?}}, 1'b0, { 47{1'b1}}}: return COUNT_WIDTH'({7'( 47), local_count[ 47]});
      {{ 79{1'b?}}, 1'b0, { 48{1'b1}}}: return COUNT_WIDTH'({7'( 48), local_count[ 48]});
      {{ 78{1'b?}}, 1'b0, { 49{1'b1}}}: return COUNT_WIDTH'({7'( 49), local_count[ 49]});
      {{ 77{1'b?}}, 1'b0, { 50{1'b1}}}: return COUNT_WIDTH'({7'( 50), local_count[ 50]});
      {{ 76{1'b?}}, 1'b0, { 51{1'b1}}}: return COUNT_WIDTH'({7'( 51), local_count[ 51]});
      {{ 75{1'b?}}, 1'b0, { 52{1'b1}}}: return COUNT_WIDTH'({7'( 52), local_count[ 52]});
      {{ 74{1'b?}}, 1'b0, { 53{1'b1}}}: return COUNT_WIDTH'({7'( 53), local_count[ 53]});
      {{ 73{1'b?}}, 1'b0, { 54{1'b1}}}: return COUNT_WIDTH'({7'( 54), local_count[ 54]});
      {{ 72{1'b?}}, 1'b0, { 55{1'b1}}}: return COUNT_WIDTH'({7'( 55), local_count[ 55]});
      {{ 71{1'b?}}, 1'b0, { 56{1'b1}}}: return COUNT_WIDTH'({7'( 56), local_count[ 56]});
      {{ 70{1'b?}}, 1'b0, { 57{1'b1}}}: return COUNT_WIDTH'({7'( 57), local_count[ 57]});
      {{ 69{1'b?}}, 1'b0, { 58{1'b1}}}: return COUNT_WIDTH'({7'( 58), local_count[ 58]});
      {{ 68{1'b?}}, 1'b0, { 59{1'b1}}}: return COUNT_WIDTH'({7'( 59), local_count[ 59]});
      {{ 67{1'b?}}, 1'b0, { 60{1'b1}}}: return COUNT_WIDTH'({7'( 60), local_count[ 60]});
      {{ 66{1'b?}}, 1'b0, { 61{1'b1}}}: return COUNT_WIDTH'({7'( 61), local_count[ 61]});
      {{ 65{1'b?}}, 1'b0, { 62{1'b1}}}: return COUNT_WIDTH'({7'( 62), local_count[ 62]});
      {{ 64{1'b?}}, 1'b0, { 63{1'b1}}}: return COUNT_WIDTH'({7'( 63), local_count[ 63]});
      {{ 63{1'b?}}, 1'b0, { 64{1'b1}}}: return COUNT_WIDTH'({7'( 64), local_count[ 64]});
      {{ 62{1'b?}}, 1'b0, { 65{1'b1}}}: return COUNT_WIDTH'({7'( 65), local_count[ 65]});
      {{ 61{1'b?}}, 1'b0, { 66{1'b1}}}: return COUNT_WIDTH'({7'( 66), local_count[ 66]});
      {{ 60{1'b?}}, 1'b0, { 67{1'b1}}}: return COUNT_WIDTH'({7'( 67), local_count[ 67]});
      {{ 59{1'b?}}, 1'b0, { 68{1'b1}}}: return COUNT_WIDTH'({7'( 68), local_count[ 68]});
      {{ 58{1'b?}}, 1'b0, { 69{1'b1}}}: return COUNT_WIDTH'({7'( 69), local_count[ 69]});
      {{ 57{1'b?}}, 1'b0, { 70{1'b1}}}: return COUNT_WIDTH'({7'( 70), local_count[ 70]});
      {{ 56{1'b?}}, 1'b0, { 71{1'b1}}}: return COUNT_WIDTH'({7'( 71), local_count[ 71]});
      {{ 55{1'b?}}, 1'b0, { 72{1'b1}}}: return COUNT_WIDTH'({7'( 72), local_count[ 72]});
      {{ 54{1'b?}}, 1'b0, { 73{1'b1}}}: return COUNT_WIDTH'({7'( 73), local_count[ 73]});
      {{ 53{1'b?}}, 1'b0, { 74{1'b1}}}: return COUNT_WIDTH'({7'( 74), local_count[ 74]});
      {{ 52{1'b?}}, 1'b0, { 75{1'b1}}}: return COUNT_WIDTH'({7'( 75), local_count[ 75]});
      {{ 51{1'b?}}, 1'b0, { 76{1'b1}}}: return COUNT_WIDTH'({7'( 76), local_count[ 76]});
      {{ 50{1'b?}}, 1'b0, { 77{1'b1}}}: return COUNT_WIDTH'({7'( 77), local_count[ 77]});
      {{ 49{1'b?}}, 1'b0, { 78{1'b1}}}: return COUNT_WIDTH'({7'( 78), local_count[ 78]});
      {{ 48{1'b?}}, 1'b0, { 79{1'b1}}}: return COUNT_WIDTH'({7'( 79), local_count[ 79]});
      {{ 47{1'b?}}, 1'b0, { 80{1'b1}}}: return COUNT_WIDTH'({7'( 80), local_count[ 80]});
      {{ 46{1'b?}}, 1'b0, { 81{1'b1}}}: return COUNT_WIDTH'({7'( 81), local_count[ 81]});
      {{ 45{1'b?}}, 1'b0, { 82{1'b1}}}: return COUNT_WIDTH'({7'( 82), local_count[ 82]});
      {{ 44{1'b?}}, 1'b0, { 83{1'b1}}}: return COUNT_WIDTH'({7'( 83), local_count[ 83]});
      {{ 43{1'b?}}, 1'b0, { 84{1'b1}}}: return COUNT_WIDTH'({7'( 84), local_count[ 84]});
      {{ 42{1'b?}}, 1'b0, { 85{1'b1}}}: return COUNT_WIDTH'({7'( 85), local_count[ 85]});
      {{ 41{1'b?}}, 1'b0, { 86{1'b1}}}: return COUNT_WIDTH'({7'( 86), local_count[ 86]});
      {{ 40{1'b?}}, 1'b0, { 87{1'b1}}}: return COUNT_WIDTH'({7'( 87), local_count[ 87]});
      {{ 39{1'b?}}, 1'b0, { 88{1'b1}}}: return COUNT_WIDTH'({7'( 88), local_count[ 88]});
      {{ 38{1'b?}}, 1'b0, { 89{1'b1}}}: return COUNT_WIDTH'({7'( 89), local_count[ 89]});
      {{ 37{1'b?}}, 1'b0, { 90{1'b1}}}: return COUNT_WIDTH'({7'( 90), local_count[ 90]});
      {{ 36{1'b?}}, 1'b0, { 91{1'b1}}}: return COUNT_WIDTH'({7'( 91), local_count[ 91]});
      {{ 35{1'b?}}, 1'b0, { 92{1'b1}}}: return COUNT_WIDTH'({7'( 92), local_count[ 92]});
      {{ 34{1'b?}}, 1'b0, { 93{1'b1}}}: return COUNT_WIDTH'({7'( 93), local_count[ 93]});
      {{ 33{1'b?}}, 1'b0, { 94{1'b1}}}: return COUNT_WIDTH'({7'( 94), local_count[ 94]});
      {{ 32{1'b?}}, 1'b0, { 95{1'b1}}}: return COUNT_WIDTH'({7'( 95), local_count[ 95]});
      {{ 31{1'b?}}, 1'b0, { 96{1'b1}}}: return COUNT_WIDTH'({7'( 96), local_count[ 96]});
      {{ 30{1'b?}}, 1'b0, { 97{1'b1}}}: return COUNT_WIDTH'({7'( 97), local_count[ 97]});
      {{ 29{1'b?}}, 1'b0, { 98{1'b1}}}: return COUNT_WIDTH'({7'( 98), local_count[ 98]});
      {{ 28{1'b?}}, 1'b0, { 99{1'b1}}}: return COUNT_WIDTH'({7'( 99), local_count[ 99]});
      {{ 27{1'b?}}, 1'b0, {100{1'b1}}}: return COUNT_WIDTH'({7'(100), local_count[100]});
      {{ 26{1'b?}}, 1'b0, {101{1'b1}}}: return COUNT_WIDTH'({7'(101), local_count[101]});
      {{ 25{1'b?}}, 1'b0, {102{1'b1}}}: return COUNT_WIDTH'({7'(102), local_count[102]});
      {{ 24{1'b?}}, 1'b0, {103{1'b1}}}: return COUNT_WIDTH'({7'(103), local_count[103]});
      {{ 23{1'b?}}, 1'b0, {104{1'b1}}}: return COUNT_WIDTH'({7'(104), local_count[104]});
      {{ 22{1'b?}}, 1'b0, {105{1'b1}}}: return COUNT_WIDTH'({7'(105), local_count[105]});
      {{ 21{1'b?}}, 1'b0, {106{1'b1}}}: return COUNT_WIDTH'({7'(106), local_count[106]});
      {{ 20{1'b?}}, 1'b0, {107{1'b1}}}: return COUNT_WIDTH'({7'(107), local_count[107]});
      {{ 19{1'b?}}, 1'b0, {108{1'b1}}}: return COUNT_WIDTH'({7'(108), local_count[108]});
      {{ 18{1'b?}}, 1'b0, {109{1'b1}}}: return COUNT_WIDTH'({7'(109), local_count[109]});
      {{ 17{1'b?}}, 1'b0, {110{1'b1}}}: return COUNT_WIDTH'({7'(110), local_count[110]});
      {{ 16{1'b?}}, 1'b0, {111{1'b1}}}: return COUNT_WIDTH'({7'(111), local_count[111]});
      {{ 15{1'b?}}, 1'b0, {112{1'b1}}}: return COUNT_WIDTH'({7'(112), local_count[112]});
      {{ 14{1'b?}}, 1'b0, {113{1'b1}}}: return COUNT_WIDTH'({7'(113), local_count[113]});
      {{ 13{1'b?}}, 1'b0, {114{1'b1}}}: return COUNT_WIDTH'({7'(114), local_count[114]});
      {{ 12{1'b?}}, 1'b0, {115{1'b1}}}: return COUNT_WIDTH'({7'(115), local_count[115]});
      {{ 11{1'b?}}, 1'b0, {116{1'b1}}}: return COUNT_WIDTH'({7'(116), local_count[116]});
      {{ 10{1'b?}}, 1'b0, {117{1'b1}}}: return COUNT_WIDTH'({7'(117), local_count[117]});
      {{  9{1'b?}}, 1'b0, {118{1'b1}}}: return COUNT_WIDTH'({7'(118), local_count[118]});
      {{  8{1'b?}}, 1'b0, {119{1'b1}}}: return COUNT_WIDTH'({7'(119), local_count[119]});
      {{  7{1'b?}}, 1'b0, {120{1'b1}}}: return COUNT_WIDTH'({7'(120), local_count[120]});
      {{  6{1'b?}}, 1'b0, {121{1'b1}}}: return COUNT_WIDTH'({7'(121), local_count[121]});
      {{  5{1'b?}}, 1'b0, {122{1'b1}}}: return COUNT_WIDTH'({7'(122), local_count[122]});
      {{  4{1'b?}}, 1'b0, {123{1'b1}}}: return COUNT_WIDTH'({7'(123), local_count[123]});
      {{  3{1'b?}}, 1'b0, {124{1'b1}}}: return COUNT_WIDTH'({7'(124), local_count[124]});
      {{  2{1'b?}}, 1'b0, {125{1'b1}}}: return COUNT_WIDTH'({7'(125), local_count[125]});
      {{  1{1'b?}}, 1'b0, {126{1'b1}}}: return COUNT_WIDTH'({7'(126), local_count[126]});
      default:                          return COUNT_WIDTH'({7'(127), local_count[127]});
    endcase
  endfunction

  function automatic logic [2:0] __calc_nlc(logic [3:0] nibble);
    logic [2:0] result;
    result[2] = ~|nibble;
    result[1] = ~|nibble[1:0];
    result[0] = ~(nibble[0] | ((~nibble[1]) & nibble[2]));
    return result;
  endfunction
endinterface
