import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_410700_2.RI3_1_410700_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-18, -11, 3]

def alpha1 := B.equivFun.symm ![-6, -4, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![29, 2, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-28, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-28, -2, 1]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-84, -6, 3]], ![![-84, -6, 3], ![-87, 19, -3]]]
 hmul := by decide
 f := ![![![![-2632617, 3300986, -1128957], ![21994375, 3102320, 0]], ![![0, 0, 0], ![-6112, 16, 0]]], ![![![-862, 1099, -376], ![7318, 1032, 0]], ![![0, 0, 0], ![-2, 0, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-28, -2, 1], ![0, 0, 0]]], ![![![-28, -2, 1], ![0, 0, 0]], ![![-29, 5, -1], ![4, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![9, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![-84, -6, 3]], ![![0, 3, 0], ![201, 11, -6]]]
 hmul := by decide
 f := ![![![![53, -50, 17], ![-339, -48, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![896, -1118, 383], ![-7487, -1056, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![0, -3, -2], ![3, 6, 0]], ![![-12, 18, 15], ![8, -44, 0]]], ![![![-3, 2, 2], ![9, -6, 0]], ![![21, -49, -38], ![4, 112, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![9, 0, 0], ![3, 1, 0]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![9, 0, 0], ![-81, -5, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![27, 0, 0], ![-252, -18, 9]], ![![9, 3, 0], ![117, 5, -3]]]
 hmul := by decide
 f := ![![![![6939, -8644, 2960], ![-57868, -8164, 0]], ![![4, 0, 0], ![-2, 2, 0]]], ![![![-88810, 110900, -37978], ![742354, 104728, 0]], ![![-60, 0, 0], ![30, -25, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![53, 3, -2], ![9, 0, 0]]], ![![![28, 2, -1], ![3, 0, 0]], ![![4, 0, 0], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![9, 0, 0], ![-81, -5, 3]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![27, 0, 0], ![-81, -5, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![27, 0, 0], ![-252, -18, 9]], ![![-243, -15, 9], ![-144, 62, -12]]]
 hmul := by decide
 f := ![![![![149, -164, 56], ![-1104, -156, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-117240, 146350, -50128], ![980104, 138268, 0]], ![![-105, 0, 0], ![5, 0, 0]]]]
 g := ![![![![222, 13, 13], ![-507, -78, 0]], ![![-1586, -92, -139], ![4894, 728, 0]]], ![![![-1503, -87, -135], ![4728, 702, 0]], ![![-908, -50, -80], ![2796, 416, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![27, 0, 0], ![-81, -5, 3]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![27, 0, 0], ![-72, -2, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![81, 0, 0], ![-756, -54, 27]], ![![-243, -15, 9], ![-144, 62, -12]]]
 hmul := by decide
 f := ![![![![-27717564149, 34599181464, -11851270490], ![231680720990, 32686581280, 0]], ![![-23007016, 0, 0], ![-557362, -80, 0]]], ![![![27711092400, -34591102888, 11848503332], ![-231626625783, -32678949280, 0]], ![![23001644, 0, 0], ![557232, 80, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![44, 0, -2], ![27, 0, 0]]], ![![![47, 1, -2], ![21, 0, 0]], ![![56, 4, -3], ![23, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![27, 0, 0], ![-72, -2, 3]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![81, 0, 0], ![-72, -2, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![81, 0, 0], ![-756, -54, 27]], ![![-216, -6, 9], ![207, 77, -21]]]
 hmul := by decide
 f := ![![![![-5678692, 7088953, -2427961], ![47465967, 6696720, 0]], ![![-5313, 0, 0], ![-9, 0, 0]]], ![![![5064164, -6321784, 2165206], ![-42329191, -5972000, 0]], ![![4738, 0, 0], ![8, 0, 0]]]]
 g := ![![![![96, 11, 1], ![-69, -21, 0]], ![![-674, -90, -14], ![743, 178, 0]]], ![![![-162, -26, -6], ![273, 54, 0]], ![![179, 17, -1], ![-36, -28, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-72, -2, 3]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![81, 0, 0], ![-99, 16, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![243, 0, 0], ![-2268, -162, 81]], ![![-216, -6, 9], ![207, 77, -21]]]
 hmul := by decide
 f := ![![![![-8208330534, 10246430517, -3509684514], ![68610236526, 9680056386, 0]], ![![-7607633, 0, 0], ![-2354, 5, 0]]], ![![![3308441322, -4129915803, 1414609850], ![-27653971757, -3901633626, 0]], ![![3066325, 0, 0], ![949, -2, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![71, -18, -2], ![81, 0, 0]]], ![![![34, -6, -1], ![30, 0, 0]], ![![27, -3, -1], ![20, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-99, 16, 3]] ![![3, 0, 0], ![-28, -2, 1]]
  ![![-18, -11, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![243, 0, 0], ![-2268, -162, 81]], ![![-297, 48, 9], ![4581, 329, -156]]]
 hmul := by decide
 f := ![![![![-653965865, 816426313, -279623121], ![5466189747, 771212618, 0]], ![![-402049, 0, 0], ![2, 0, 0]]]]
 g := ![![![![20, 5, 1]], ![![-8, 0, 1]]], ![![![50, 17, 4]], ![![47, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, 0, 0], ![11, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![54, 0, 0], ![11, 1, 0]] ![![54, 0, 0], ![11, 1, 0]]
  ![![1458, 0, 0], ![-17321, -783, 643]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![2916, 0, 0], ![594, 54, 0]], ![![594, 54, 0], ![121, 23, 3]]]
 hmul := by decide
 f := ![![![![157585999955547, -3007040426299, 0], ![32045165909010, 161481870010494, -43999230527928]], ![![0, 0, 0], ![-8162601662592, -466647480, -18225]]], ![![![-1855191716855613, 35400584396405, 0], ![-377253857426171, -1901056107460793, 517983882111703]], ![![0, 0, 0], ![96094773626488, 5493638647, 214555]]]]
 g := ![![![![100439746661482, 277844028061410, 273227308752290], ![-1221936602242320, -164895623261568, 4374]], ![![19839952009120, 54882776657844, 53970832008779], ![-241370218028682, -32571978337944, 864]]], ![![![19839952009120, 54882776657844, 53970832008779], ![-241370218028682, -32571978337944, 864]], ![![3903694740195, 10798695783995, 10619262208032], ![-47491831033407, -6408839103292, 170]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![1458, 0, 0], ![-17321, -783, 643]] ![![54, 0, 0], ![11, 1, 0]]
  ![![-6, -4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![78732, 0, 0], ![16038, 1458, 0]], ![![-935334, -42282, 34722], ![-61288, -354, 4724]]]
 hmul := by decide
 f := ![![![![3246770218667595418630295265155664473876137280, -61279625574710053004886680302853846624677597, 0], ![660244310736459991702377059933508432703941352, 3319594063623041171605487894893503211300444396, -906578802109293427934892452200901586433433909]], ![![570427785183879655157716685905780276409648, -3031323358001802262024291666636276, 1150833247532540835769477], ![677292740081334336955, -437597256, 10]]]]
 g := ![![![![2556, 122, -48]], ![![342, 38, -3]]], ![![![-12951, -1043, 633]], ![![-282, 9, 71]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-30, -9, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![11, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-17321, -783, 643]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-28, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-28, -2, 1]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![16, -14, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![162, 0, 0], ![33, 3, 0]], ![![-1512, -108, 54], ![-107, -11, 5]]]
 hmul := by decide
 f := ![![![![175449143, -3303447, 0], ![35678493, 179390547, -48989241]], ![![39440, 0, 0], ![54, 0, 0]]], ![![![54093650, -1018504, 0], ![11000259, 55308852, -15104133]], ![![12160, 0, 0], ![16, 0, 0]]]]
 g := ![![![![645016633, 170803777, 146369660], ![144123057, 184757949, 189]], ![![129686416, 34341640, 29428941], ![28977238, 37147253, 38]]], ![![![-5958744274, -1577906566, -1352181193], ![-1331426574, -1706817006, -1746]], ![![-419774697, -111158512, -95256886], ![-93794738, -120239858, -123]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![16, -14, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![-28, -2, 1]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![-451, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4374, 0, 0], ![-51963, -2349, 1929]], ![![-40824, -2916, 1458], ![26038, 16384, -4264]]]
 hmul := by decide
 f := ![![![![396112273469764602168709450, 1095755747333464363681304496, 1077548421479247049043753868], ![-4819049248230959820570249642, -650312076648129228307615680, 5453359524166761]], ![![273680592902, 0, 0], ![-2916, 0, 0]]], ![![![-122528557990472620218953297, -338947769667607315717481137, -333315736703220554724481901], ![1490666143966078166208178763, 201159636629050625094652408, -1686875977981446]], ![![-84657029444, 0, 0], ![902, 0, 0]]]]
 g := ![![![![394018119, -882467523, -6354093], ![-121279356, -3130209360, 12393]], ![![-4469598160, 10010394717, 72078549], ![1375755617, 35507971020, -140573]]], ![![![-3415167304, 7648824620, 55074371], ![1051198560, 27131222160, -107406]], ![![871588757, -1952065065, -14055611], ![-268277256, -6924189520, 27353]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-451, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![-21, 3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![162, 0, 0], ![33, 3, 0]], ![![0, 54, 0], ![0, 12, 3]]]
 hmul := by decide
 f := ![![![![384, -10, 0], ![90, 396, -108]], ![![7, 0, 0], ![0, 0, 0]]], ![![![-194, 5, 0], ![-35, -198, 54]], ![![-4, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1318, 230, 0], ![-495, -315, -135]], ![![264, 46, 0], ![-98, -63, -27]]], ![![![-83, -15, 0], ![45, 21, 9]], ![![-13, -4, 0], ![24, 5, 2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![-21, 3, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![3, 0, 0], ![0, 1, 0]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![-819, -177, 21]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4374, 0, 0], ![-51963, -2349, 1929]], ![![0, 1458, 0], ![129243, 8259, -2349]]]
 hmul := by decide
 f := ![![![![-75796583417345869704, -209674245082779604026, -206190250303151216422], ![922131155230958940714, 124438036552608216672, -1043510769]], ![![-4294286, 0, 0], ![0, 0, 0]]], ![![![45848446943325286705, 126829443592831298261, 124722016811797005641], ![-557786109073071680813, -75271080296584794024, 631207186]], ![![2597562, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2369144581866, -257628041322, -371452937805], ![-1304890096113, -1071527447925, 11664]], ![![-28145372223138, 3060614019021, 4412850646104], ![15502058322006, 12729716498983, -138568]]], ![![![-253995, 27665, 39841], ![140211, 114939, 0]], ![![70003508657504, -7612396037093, -10975695256688], ![-38556906098899, -31661504139078, 344648]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-819, -177, 21]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![9, 0, 0], ![3, 1, 0]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![663, 33, -24]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![486, 0, 0], ![99, 9, 0]], ![![162, 54, 0], ![33, 15, 3]]]
 hmul := by decide
 f := ![![![![-1042079, 19317, 0], ![-211887, -1066767, 290937]], ![![6931, 0, 0], ![-18, 0, 0]]], ![![![-13331665, 247137, 0], ![-2711102, -13647581, 3722074]], ![![88669, 0, 0], ![-221, 0, 0]]]]
 g := ![![![![6866783, 10606775, 15967366], ![83695365, 11579175, -351]], ![![1388976, 2145531, 3229871], ![16929854, 2342229, -71]]], ![![![2230098, 3444944, 5186010], ![27183240, 3760774, -114]], ![![449761, 695020, 1046300], ![5484318, 758748, -23]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![663, 33, -24]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![9, 0, 0], ![3, 1, 0]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![105, -3, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![13122, 0, 0], ![-155889, -7047, 5787]], ![![4374, 1458, 0], ![77280, 5910, -420]]]
 hmul := by decide
 f := ![![![![48971722361174640073604526, 135469284420926584195666452, 133218296080872147493756896], ![-595783462509938727915938910, -80398676332899667169671536, 220934839912929]], ![![-340948817612, 0, 0], ![-486, 0, 0]]], ![![![3526768771656721068575345, 9756014670890705904425441, 9593906519486145655720909], ![-42906199923967007335428937, -5790025902748454082142676, 15910939138086]], ![![-24553917745, 0, 0], ![-35, 0, 0]]]]
 g := ![![![![124073383334, 46551639506, -1879524887], ![8835673428, -301536828414, 38637]], ![![-1407384437058, -528042769508, 21319754519], ![-100224470671, 3420380972034, -438257]]], ![![![27577666203, 10346986131, -417760108], ![1963896516, -67022287812, 8586]], ![![674853379360, 253201213600, -10223012280], ![48058527150, -1640103156590, 210145]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![105, -3, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-81, -5, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![9, 0, 0], ![-81, -5, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![-9, 9, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![486, 0, 0], ![99, 9, 0]], ![![-4374, -270, 162], ![-288, -18, 18]]]
 hmul := by decide
 f := ![![![![7250172, -136584, 0], ![1474365, 7412733, -2024415]], ![![1687, 0, 0], ![0, 0, 0]]], ![![![-5178672, 97559, 0], ![-1053086, -5294781, 1446003]], ![![-1205, 0, 0], ![0, 0, 0]]]]
 g := ![![![![4437, 1017, 0], ![-567, -45, -135]], ![![888, 203, 0], ![-110, -9, -27]]], ![![![-39436, -9050, 0], ![5070, 406, 1200]], ![![-2596, -596, 0], ![335, 27, 79]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![-9, 9, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![9, 0, 0], ![-81, -5, 3]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![531, 603, -27]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![13122, 0, 0], ![-155889, -7047, 5787]], ![![-118098, -7290, 4374], ![155394, 55062, -13212]]]
 hmul := by decide
 f := ![![![![16784788421435346149, 46431351951207121809, 45659838081462456305], ![-204201504073454345352, -27556203999903866496, 75724227]], ![![3928, 0, 0], ![0, 0, 0]]], ![![![8580395845462724210, 23735740325005889614, 23341341883008257198], ![-104387954926587824403, -14086751192856497564, 38710279]], ![![2008, 0, 0], ![0, 0, 0]]]]
 g := ![![![![24626866101, -3343081029, -9006508494], ![7753198824, 7374695220, -3645]], ![![-289921459321, 39356648831, 106029734884], ![-91275060553, -86819101920, 42911]]], ![![![-218905552398, 29716285854, 80057880992], ![-68917346154, -65552869080, 32400]], ![![270970419133, -36784057555, -99098982798], ![85308764432, 81144074320, -40106]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![531, 603, -27]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-81, -5, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![27, 0, 0], ![-81, -5, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![252, 36, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![1458, 0, 0], ![297, 27, 0]], ![![-4374, -270, 162], ![-288, -18, 18]]]
 hmul := by decide
 f := ![![![![188505124, -3551192, 0], ![38333457, 192731689, -52634963]], ![![131587, 0, 0], ![6, 0, 0]]], ![![![863374363, -16264851, 0], ![175571392, 882732481, -241073960]], ![![602683, 0, 0], ![28, 0, 0]]]]
 g := ![![![![5094, -8325, -2394], ![18684, 2754, 0]], ![![1019, -1698, -487], ![3810, 561, 0]]], ![![![-15338, 24962, 7187], ![-56040, -8262, 0]], ![![-1028, 1641, 474], ![-3686, -544, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![252, 36, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![27, 0, 0], ![-81, -5, 3]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![315, -9, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![39366, 0, 0], ![-467667, -21141, 17361]], ![![-118098, -7290, 4374], ![155394, 55062, -13212]]]
 hmul := by decide
 f := ![![![![8532323447473055074980617, 23602758820180922986971273, 23210570028697253297604673], ![-103803112524986361990400716, -14007828970459883447146944, 12759225050817]], ![![1985557576, 0, 0], ![-4212, 0, 0]]], ![![![1843403176824199844746360, 5099361370767387143588936, 5014629226166146802500574], ![-22426597933235937757259733, -3026382741292269258603928, 2756622640631]], ![![428978480, 0, 0], ![-910, 0, 0]]]]
 g := ![![![![153979505, 60217271, -2659346], ![32879196, -129671604, 117369]], ![![-1746591100, -683044992, 30164981], ![-372947389, 1470866040, -1331309]]], ![![![-433427730, -169501974, 7485632], ![-92549250, 365004792, -330372]], ![![392476185, 153486973, -6778366], ![83805096, -330518080, 299138]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![315, -9, 9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-72, -2, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![27, 0, 0], ![-72, -2, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![27, 27, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![1458, 0, 0], ![297, 27, 0]], ![![-3888, -108, 162], ![-189, 27, 27]]]
 hmul := by decide
 f := ![![![![35916, -678, 0], ![7309, 36717, -10029]], ![![28, 0, 0], ![0, 0, 0]]], ![![![-41023, 774, 0], ![-8329, -41934, 11454]], ![![-32, 0, 0], ![0, 0, 0]]]]
 g := ![![![![22, -5, 0], ![10, 0, 0]], ![![4, -1, 0], ![3, 0, 0]]], ![![![-226, -174, -24], ![308, 18, 0]], ![![-24, -23, -4], ![41, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![27, 27, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![27, 0, 0], ![-72, -2, 3]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![17631, 1377, -675]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![39366, 0, 0], ![-467667, -21141, 17361]], ![![-104976, -2916, 4374], ![387234, 72792, -14472]]]
 hmul := by decide
 f := ![![![![149336181701105860314781, 413105047120759464898677, 406240800003699226996685], ![-1816804129449952444774140, -245170697670884082263040, 223317134649]], ![![38649556, 0, 0], ![0, 0, 0]]], ![![![1856057125893455062267477, 5134365682294388303647805, 5049051898117067833031392], ![-22580544195025902989276755, -3047157194517613521413384, 2775545446374]], ![![480364390, 0, 0], ![0, 0, 0]]]]
 g := ![![![![275882221, -460899807, 255311995], ![2782639062, 364564152, -2187]], ![![-3228091737, 5392974059, -2987397584], ![-32559572671, -4265753772, 25590]]], ![![![-728875214, 1217686386, -674528253], ![-7351666920, -963169920, 5778]], ![![2543752182, -4249690932, 2354084478], ![25657108568, 3361435624, -20165]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![17631, 1377, -675]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-72, -2, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![81, 0, 0], ![-72, -2, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![162, 0, 0], ![-756, -54, 27]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![4374, 0, 0], ![891, 81, 0]], ![![-3888, -108, 162], ![-189, 27, 27]]]
 hmul := by decide
 f := ![![![![239387038094, -4518188908, 0], ![48680356155, 244718564353, -66843270131]], ![![560139111, 0, 0], ![480, 0, 0]]], ![![![-1117014998844, 21082531522, 0], ![-227149675055, -1141892681586, 311900493441]], ![![-2613691173, 0, 0], ![-2240, 0, 0]]]]
 g := ![![![![814331581, -244288552, 77097773], ![-3705934854, -540558036, 0]], ![![165881632, -49762264, 15705033], ![-754909344, -110113191, 0]]], ![![![-723849294, 217145090, -68531262], ![3294159906, 480495388, 0]], ![![-35187383, 10555753, -3331409], ![160134097, 23357607, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![162, 0, 0], ![-756, -54, 27]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![81, 0, 0], ![-72, -2, 3]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![-513, -27, 27]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![118098, 0, 0], ![-1403001, -63423, 52083]], ![![-104976, -2916, 4374], ![387234, 72792, -14472]]]
 hmul := by decide
 f := ![![![![6867457185610111651926218379, 18997279774822350581301981927, 18681616667169750646169246585], ![-83548570959292520413365181992, -11274556843789144004955140064, 3416812678714905]], ![![1774046042758, 0, 0], ![-54, 0, 0]]], ![![![-2416330490502928432405456029, -6684236263271253543568913991, -6573169478123160572506238431], ![29396755449732114303283876121, 3966978567502473791208955820, -1202213342256509]], ![![-624202150638, 0, 0], ![19, 0, 0]]]]
 g := ![![![![941801056898, 104480294324, -9632470010], ![-333487645236, -284544415782, 353565]], ![![-10682811324450, -1185115755887, 109260718041], ![3782736882209, 3227575808088, -4010465]]], ![![![-813903189563, -90291727937, 8324367454], ![288199568502, 245902896252, -305550]], ![![2507619763232, 278187042846, -25647212852], ![-887937217664, -757622000222, 941385]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-513, -27, 27]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-99, 16, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![81, 0, 0], ![-99, 16, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![162, 0, 0], ![81, 27, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![4374, 0, 0], ![891, 81, 0]], ![![-5346, 864, 162], ![-486, 216, 81]]]
 hmul := by decide
 f := ![![![![4041141257, -78237781, 0], ![821746612, 4133326920, -1128475542]], ![![6625101, 0, 0], ![0, 0, 0]]], ![![![1346983642, -26078033, 0], ![273902681, 1377710758, -376140800]], ![![2208263, 0, 0], ![0, 0, 0]]]]
 g := ![![![![21, -2, 0], ![12, 0, 0]], ![![4, 0, 0], ![3, 0, 0]]], ![![![-27, 6, 0], ![-12, 2, 0]], ![![-1, 0, -1], ![-4, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![162, 0, 0], ![81, 27, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![81, 0, 0], ![-99, 16, 3]] ![![1458, 0, 0], ![-17321, -783, 643]]
  ![![1458, 0, 0], ![-10287, -243, 405]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![118098, 0, 0], ![-1403001, -63423, 52083]], ![![-144342, 23328, 4374], ![3181275, 242595, -74115]]]
 hmul := by decide
 f := ![![![![155679425794783971354, 430652208972520911636, 423496394234145087810], ![-1893975193638121723182, -255584634616955457216, 77456259]], ![![27496, 0, 0], ![0, 0, 0]]], ![![![-1107670205596696320468, -3064121147787829643440, -3013207016122692249427], ![13475768435179256876075, 1818502883911619307532, -551106801]], ![![-195636, 0, 0], ![0, 0, 0]]]]
 g := ![![![![854881374047, 2239771995519, 1289913053456], ![-6046649179056, -779414244318, 1060695]], ![![-10002932949992, -26207483020311, -15093221325044], ![70751601505295, 9119895067260, -12411150]]], ![![![-1101143498178, -2884973804910, -1661492945398], ![7788482275914, 1003936866138, -1366245]], ![![22443079145316, 58800415694139, 33863903961625], ![-158741821040481, -20461851320310, 27846275]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-10287, -243, 405]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
