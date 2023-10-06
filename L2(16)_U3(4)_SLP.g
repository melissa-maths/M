# Supplementary GAP code for the paper 
# "Indeed, the Monster has no almost simple maximal subgroups with socle isomorphic to PSL2(16) or PSU3(4)"
# by H. Dietrich, M. Lee, and T. Popiel.
#
# Version 1.0
# 6 October 2023
#
# This code can be used the verify a part of the proof of Proposition 3.
# Specifically, it shows that the group A_B constructed in Proposition 3 is an A5 of type "B".
#
# The functions A5_in_A12_gen_1 and A5_in_A12_gen_2 are SLPs that take generators 
# for A12 satisfying the presentation in the proof of Proposition 2, and output generators 
# for a subgroup of A12 that is isomorphic to A5 and has orbits of lengths 6 and 6 on 12 points. 
#
# These SLPs should be applied to the elements a = y3 = (1,2,3) and b = y10 = (1,3)(2,4,5,6,7,8,9,10,11,12).
# Commands for verifying the claims made in the proof of Proposition 3 are given below the function definitions.
# This file should be used in conjunction with the corresponding Python file also available at 
# https://github.com/melissa-maths/M 
# which includes Python code for constructing mmgroup copies of these groups A5 < A12.

A5_in_A12_gen_1 := function(a,b)
	local w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86, w87, w88, w89, w90, w91, w92;
	b := a^2 * b;
	w3 := b * a; 
	w4 := b * w3; 
	w5 := a * w3; 
	w6 := w4 * w5; 
	w10 := w5 * a; 
	w11 := w6 * w10; 
	w16 := a^2; 
	w17 := w11 * w16; 
	w12 := b^-4; 
	w7 := b^-3; 
	w8 := w6 * w7; 
	w9 := w8^-1; 
	w13 := w12 * w9; 
	w18 := w17 * w13; 
	w19 := w18^-1; 
	w20 := w10 * w16; 
	w21 := w17 * w20; 
	w22 := b^-5; 
	w23 := w22 * w9; 
	w24 := w21 * w23; 
	w26 := w19 * w24; 
	w14 := w11 * w13; 
	w27 := w26 * w14; 
	w28 := w10 * a; 
	w29 := w21 * w28; 
	w30 := w20 * a; 
	w31 := w29 * w30; 
	w39 := a * w28; 
	w40 := w31 * w39; 
	w49 := w39 * w28; 
	w50 := w40 * w49; 
	w55 := w39 * w30; 
	w56 := w50 * w55; 
	w32 := b^3; 
	w33 := a * w19; 
	w15 := w14^-1; 
	w34 := w15 * w9; 
	w35 := w33 * w34; 
	w36 := w32 * w35; 
	w37 := w31 * w36; 
	w57 := w37^-2; 
	w58 := a * w57; 
	w59 := w58 * w9; 
	w25 := w24^-1; 
	w38 := w37^-1; 
	w60 := w25 * w38; 
	w44 := w9 * w38; 
	w51 := w15 * w44; 
	w52 := w33 * w51; 
	w53 := w50 * w52; 
	w54 := w53^-1; 
	w41 := b^2; 
	w42 := w41 * a; 
	w43 := w19 * w15; 
	w45 := w43 * w44; 
	w46 := w42 * w45; 
	w47 := w40 * w46; 
	w48 := w47^-1; 
	w61 := w54 * w48; 
	w62 := w60 * w61; 
	w63 := w59 * w62; 
	w64 := w56 * w63; 
	w66 := w27 * w64; 
	w67 := w66 * w24; 
	w68 := w67 * w14; 
	w69 := w68 * w47; 
	w70 := w49 * w39; 
	w71 := w56 * w70; 
	w77 := w55 * w49; 
	w78 := w71 * w77; 
	w1 := a^-1; 
	w79 := w1 * w9; 
	w80 := w19 * w34; 
	w81 := w79 * w80; 
	w82 := w19 * w38; 
	w65 := w64^-1; 
	w72 := w38 * w9; 
	w73 := w65 * w60; 
	w74 := w72 * w73; 
	w75 := w71 * w74; 
	w83 := w75^-2; 
	w84 := w65 * w83; 
	w85 := w82 * w84; 
	w86 := w81 * w85; 
	w87 := w78 * w86; 
	w89 := w69 * w87; 
	w90 := w89 * w87; 
	w91 := w90 * w37; 
	w92 := w91 * w18; 
	return w92;
end;

A5_in_A12_gen_2 := function(a,b) 
	local w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86, w87, w88, w89, w90, w91, w92, w93, w94, w95, w96, w97, w98, w99, w100, w101, w102, w103, w104, w105, w106, w107, w108, w109, w110, w111, w112, w113, w114, w115, w116, w117;
	b := a^2 * b;
	w3 := b * a; 
	w4 := b * w3; 
	w5 := a * w3; 
	w6 := w4 * w5; 
	w10 := w5 * a; 
	w11 := w6 * w10; 
	w16 := a^2; 
	w17 := w11 * w16; 
	w20 := w10 * w16; 
	w21 := w17 * w20; 
	w28 := w10 * a; 
	w29 := w21 * w28; 
	w30 := w20 * a; 
	w31 := w29 * w30; 
	w39 := a * w28; 
	w40 := w31 * w39; 
	w49 := w39 * w28; 
	w50 := w40 * w49; 
	w55 := w39 * w30; 
	w56 := w50 * w55; 
	w70 := w49 * w39; 
	w71 := w56 * w70; 
	w77 := w55 * w49; 
	w78 := w71 * w77; 
	w93 := w55 * w70; 
	w94 := w78 * w93; 
	w22 := b^-5; 
	w12 := b^-4; 
	w7 := b^-3; 
	w8 := w6 * w7; 
	w9 := w8^-1; 
	w13 := w12 * w9; 
	w18 := w17 * w13; 
	w19 := w18^-1; 
	w14 := w11 * w13; 
	w15 := w14^-1; 
	w43 := w19 * w15; 
	w95 := w22 * w43; 
	w32 := b^3; 
	w33 := a * w19; 
	w34 := w15 * w9; 
	w35 := w33 * w34; 
	w36 := w32 * w35; 
	w37 := w31 * w36; 
	w38 := w37^-1; 
	w57 := w37^-2; 
	w58 := a * w57; 
	w59 := w58 * w9; 
	w23 := w22 * w9; 
	w24 := w21 * w23; 
	w25 := w24^-1; 
	w60 := w25 * w38; 
	w44 := w9 * w38; 
	w51 := w15 * w44; 
	w52 := w33 * w51; 
	w53 := w50 * w52; 
	w54 := w53^-1; 
	w41 := b^2; 
	w42 := w41 * a; 
	w45 := w43 * w44; 
	w46 := w42 * w45; 
	w47 := w40 * w46; 
	w48 := w47^-1; 
	w61 := w54 * w48; 
	w62 := w60 * w61; 
	w63 := w59 * w62; 
	w64 := w56 * w63; 
	w65 := w64^-1; 
	w96 := w38 * w65; 
	w97 := w9 * w96; 
	w72 := w38 * w9; 
	w73 := w65 * w60; 
	w74 := w72 * w73; 
	w75 := w71 * w74; 
	w83 := w75^-2; 
	w1 := a^-1; 
	w79 := w1 * w9; 
	w80 := w19 * w34; 
	w81 := w79 * w80; 
	w82 := w19 * w38; 
	w84 := w65 * w83; 
	w85 := w82 * w84; 
	w86 := w81 * w85; 
	w87 := w78 * w86; 
	w88 := w87^-1; 
	w98 := w88 * w19; 
	w99 := w83 * w98; 
	w100 := w97 * w99; 
	w101 := w95 * w100; 
	w102 := w94 * w101; 
	w103 := w102^-1; 
	w104 := w103 * w18; 
	w105 := w104 * w24; 
	w106 := w105 * w64; 
	w107 := w106 * w24; 
	w108 := w107 * w14; 
	w109 := w108 * w48; 
	w110 := w109 * w88; 
	w111 := w110 * w88; 
	w112 := w111 * w38; 
	w76 := w75^-1; 
	w113 := w112 * w76; 
	w114 := w113 * w8; 
	w115 := w114 * w75; 
	w116 := w115 * b; 
	w117 := w116 * b; 
	return w117;
end;

# Define the groups A5 < A12 and check the claims made in the proof of Proposition 3.
y3 := (1,2,3);;
y10 := (1,3)(2,4,5,6,7,8,9,10,11,12);;
Y := Group(y3, y10);;
A := Group(A5_in_A12_gen_1(y3, y10), A5_in_A12_gen_2(y3, y10));;

# Should output true:
StructureDescription(Y) = "A12" and StructureDescription(A) = "A5" and IsSubgroup(Y,A) and List(Orbits(A), Size) = [6,6];