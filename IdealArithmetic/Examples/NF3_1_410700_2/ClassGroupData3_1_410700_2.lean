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
  ![![1458, 0, 0], ![-173, 633, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![2916, 0, 0], ![594, 54, 0]], ![![594, 54, 0], ![121, 23, 3]]]
 hmul := by decide
 f := ![![![![157585999955547, -3007040426299, 0], ![32045165909010, 161481870010494, -43999230527928]], ![![0, 0, 0], ![-8162601662592, -466647480, -18225]]], ![![![-32381655628425, 617903542019, 0], ![-6584820525371, -33182200870562, 9041208808351]], ![![0, 0, 0], ![1677297197368, 95889343, 3745]]]]
 g := ![![![![39266931878, 76772456538, 338544246810], ![28904205564, -259940189016, -21870]], ![![7756431360, 15164929746, 66872939821], ![5709473892, -51346211850, -4320]]], ![![![7756431360, 15164929746, 66872939821], ![5709473892, -51346211850, -4320]], ![![1526149799, 2983840266, 13157870603], ![1123392336, -10102842993, -850]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![1458, 0, 0], ![-173, 633, 1]] ![![54, 0, 0], ![11, 1, 0]]
  ![![-6, -4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![78732, 0, 0], ![16038, 1458, 0]], ![![-9342, 34182, 54], ![-1702, 7464, 1910]]]
 hmul := by decide
 f := ![![![![-3953908687287244157304329555356797555455, 93454286474295857457300141387617014703, 0], ![-803695208771951664312783795695132520278, -4051023026530452777992988939890679736588, 1104957703925970864712047251832417865448]], ![![-39831540176400168568849939805286574654, 136189136659504293666608624008238, 308998040958200555494972219], ![-8219429627006800608929, 1679202050, 10]]]]
 g := ![![![![2556, 122, -48]], ![![342, 38, -3]]], ![![![-4473, 295, 165]], ![![-297, 108, 50]]]]
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

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-173, 633, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-28, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-28, -2, 1]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![-514, -28, 19]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![162, 0, 0], ![33, 3, 0]], ![![-1512, -108, 54], ![-107, -11, 5]]]
 hmul := by decide
 f := ![![![![175449143, -3303447, 0], ![35678493, 179390547, -48989241]], ![![39440, 0, 0], ![54, 0, 0]]], ![![![-1665521754, 31359296, 0], ![-338692191, -1702937060, 465050113]], ![![-374400, 0, 0], ![-514, 0, 0]]]]
 g := ![![![![984281816, 731667872, 1302095533], ![-9290143071, -1264279023, 459]], ![![182275835, 135494770, 241130017], ![-1720405609, -234126942, 85]]], ![![![-8530475702, -6341146484, -11284872342], ![80514889956, 10957127958, -3978]], ![![-583281284, -433583488, -771616697], ![5505302245, 749206773, -272]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![-514, -28, 19]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![-28, -2, 1]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![-451, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4374, 0, 0], ![-519, 1899, 3]], ![![-40824, -2916, 1458], ![131608, 7294, -3958]]]
 hmul := by decide
 f := ![![![![701028894438306390485965, 1370611560591017242921875, 6043999069990690037944641], ![516024086547515500174230, -4640688109358640640364040, -390443369759299305]], ![![1152627564806, 0, 0], ![-2916, 0, 0]]], ![![![-216847758794621229086026, -423968323488720939075683, -1869577221256173417595123], ![-159620619834120065308438, 1435494062745555119513241, 120775007050689678]], ![![-356539803332, 0, 0], ![902, 0, 0]]]]
 g := ![![![![394018119, -882467523, -6354093], ![-121279356, -3130209360, 12393]], ![![-217592921, 487335458, 3508993], ![66976679, 1728632460, -6851]]], ![![![-3415167304, 7648824620, 55074371], ![1051198560, 27131222160, -107406]], ![![11199297328, -25082652574, -180604390], ![-3447173868, -88970927320, 352223]]]]
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
  ![![3, 0, 0], ![0, 1, 0]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![15609, 771, -567]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4374, 0, 0], ![-519, 1899, 3]], ![![0, 1458, 0], ![201, 501, 1899]]]
 hmul := by decide
 f := ![![![![-31851037734336139, -62273325509295105, -274607286478815779], ![-23445399729643434, 210848273526846348, 17739683073]], ![![-4294286, 0, 0], ![0, 0, 0]]], ![![![-346988197198298087, -678411458120837854, -2991597575801447482], ![-255416387140593024, 2297000899113047485, 193257773882]], ![![-46782354, 0, 0], ![0, 0, 0]]]]
 g := ![![![![18110944000, 23597913398, 32855138214], ![193593201606, 26746251840, -61965]], ![![-3721563958, -4849063733, -6751302714], ![-39780880019, -5496006208, 12733]]], ![![![-1207400082, -1573194414, -2190342409], ![-12906213084, -1783083456, 4131]], ![![417366755, 543819990, 757155624], ![4461407563, 616374528, -1428]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![15609, 771, -567]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![9, 0, 0], ![3, 1, 0]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![-402, -6, 15]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![486, 0, 0], ![99, 9, 0]], ![![162, 54, 0], ![33, 15, 3]]]
 hmul := by decide
 f := ![![![![-1042079, 19317, 0], ![-211887, -1066767, 290937]], ![![6931, 0, 0], ![-18, 0, 0]]], ![![![7869503, -145883, 0], ![1600394, 8055997, -2197094]], ![![-52341, 0, 0], ![134, 0, 0]]]]
 g := ![![![![703174, 2099548, 1193537], ![-5136147, -697275, 189]], ![![141383, 422138, 239974], ![-1032680, -140195, 38]]], ![![![223314, 666564, 378920], ![-1630608, -221370, 60]], ![![44738, 133317, 75783], ![-326119, -44275, 12]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![-402, -6, 15]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![9, 0, 0], ![3, 1, 0]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![105, -3, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![13122, 0, 0], ![-1557, 5697, 9]], ![![4374, 1458, 0], ![-318, 2400, 1902]]]
 hmul := by decide
 f := ![![![![-1128523518596140004875, -2206424575734064727241, -9729691815802240255123], ![-830700877598307950166, 7470627409839140848656, 628539877821969]], ![![18301302010, 0, 0], ![3888, 0, 0]]], ![![![-81272852534043924634, -158900028414293453999, -700702993882731339173], ![-59824566180892241710, 538012004013825559365, 45265542064677]], ![![1318004450, 0, 0], ![280, 0, 0]]]]
 g := ![![![![124073383334, 46551639506, -1879524887], ![8835673428, -301536828414, 38637]], ![![-68566588354, -25725800460, 1038680544], ![-4882851943, 166638089718, -21359]]], ![![![27577666203, 10346986131, -417760108], ![1963896516, -67022287812, 8586]], ![![-25690146746, -9638799374, 389167032], ![-1829479692, 62435029666, -8003]]]]
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
  ![![9, 0, 0], ![-81, -5, 3]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![7101, 765, -261]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![13122, 0, 0], ![-1557, 5697, 9]], ![![-118098, -7290, 4374], ![394506, 24282, -9972]]]
 hmul := by decide
 f := ![![![![7205904321424288, 14088571592152836, 62126510565624028], ![5304232428527232, -47701820519682444, -4013384031]], ![![3928, 0, 0], ![0, 0, 0]]], ![![![36440440580635534, 71246263212721197, 314175336746821981], ![26823637674863770, -241229314003999231, -20295784649]], ![![19864, 0, 0], ![0, 0, 0]]]]
 g := ![![![![80892240, -87382802, -15483266], ![350899857, 49740399, -1458]], ![![-9599079, 10369001, 1837285], ![-41638449, -5902298, 173]]], ![![![-728033340, 786444088, 139349412], ![-3158095068, -447663186, 13122]], ![![2431991188, -2627114232, -465496203], ![10549607128, 1495417478, -43834]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![7101, 765, -261]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-81, -5, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![27, 0, 0], ![-81, -5, 3]] ![![54, 0, 0], ![11, 1, 0]]
  ![![54, 0, 0], ![-252, -36, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![1458, 0, 0], ![297, 27, 0]], ![![-4374, -270, 162], ![-288, -18, 18]]]
 hmul := by decide
 f := ![![![![188505124, -3551192, 0], ![38333457, 192731689, -52634963]], ![![131587, 0, 0], ![6, 0, 0]]], ![![![-863374374, 16264850, 0], ![-175571338, -882732481, 241073960]], ![![-602683, 0, 0], ![-28, 0, 0]]]]
 g := ![![![![5122, -8321, -2395], ![-18678, -2754, 0]], ![![1047, -1694, -488], ![-3804, -561, 0]]], ![![![-15310, 24966, 7186], ![56046, 8262, 0]], ![![-1000, 1645, 473], ![3692, 544, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54, 0, 0], ![-252, -36, 9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![27, 0, 0], ![-81, -5, 3]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![315, -9, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![39366, 0, 0], ![-4671, 17091, 27]], ![![-118098, -7290, 4374], ![394506, 24282, -9972]]]
 hmul := by decide
 f := ![![![![8497880577875433552567, 16614569603294896913433, 73265428453876292335001], ![6255250101074825812890, -56254476335231298657312, -4732960499947449]], ![![4574724520, 0, 0], ![-4212, 0, 0]]], ![![![1835961837191697871829, 3589567475498804013926, 15828950453484164070292], ![1351442911255187498916, -12153744780973326489023, -1022553185492251]], ![![988366400, 0, 0], ![-910, 0, 0]]]]
 g := ![![![![153979505, 60217271, -2659346], ![32879196, -129671604, 117369]], ![![-85112745, -33285293, 1469965], ![-18173923, 71676432, -64883]]], ![![![-433427730, -169501974, 7485632], ![-92549250, 365004792, -330372]], ![![1448138590, 566328218, -25010471], ![309219234, -1219528648, 1103816]]]]
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
  ![![27, 0, 0], ![-72, -2, 3]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![10665, 675, -405]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![39366, 0, 0], ![-4671, 17091, 27]], ![![-104976, -2916, 4374], ![393552, 31482, -4266]]]
 hmul := by decide
 f := ![![![![64554372855566095082, 126213014077679609898, 556562750263642005426], ![47518171575735187224, -427338606004164184248, -35954058678489]], ![![38649556, 0, 0], ![0, 0, 0]]], ![![![482843043397958162294, 944027075749704480301, 4162885336683487468412], ![355418503277366023794, -3196336111050925986655, -268923178196960]], ![![289084510, 0, 0], ![0, 0, 0]]]]
 g := ![![![![61074921832, 8402892890, 40579904850], ![439369776360, 58656413088, -3645]], ![![-12549908682, -1726658573, -8338514101], ![-90283382629, -12052944176, 749]]], ![![![-161961677757, -22283231607, -107611917562], ![-1165143790602, -155548149120, 9666]], ![![600813378294, 82661922614, 399197394868], ![4322219846638, 577021739840, -35857]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![10665, 675, -405]] i)) := by 
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
  ![![81, 0, 0], ![-72, -2, 3]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![-513, -27, 27]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![118098, 0, 0], ![-14013, 51273, 81]], ![![-104976, -2916, 4374], ![393552, 31482, -4266]]]
 hmul := by decide
 f := ![![![![2915061423626268302870451, 5699361208583821389022161, 25132528306809938264112203], ![2145763063822376173606902, -19297194443761733673891408, -1623566106247550805]], ![![1738088775478, 0, 0], ![-54, 0, 0]]], ![![![-1025671043570174515788668, -2005333304853543207448075, -8842937691493250212574161], ![-754991652349894313644318, 6789762096500927806958771, 571255455889696045]], ![![-611550519558, 0, 0], ![19, 0, 0]]]]
 g := ![![![![941801056898, 104480294324, -9632470010], ![-333487645236, -284544415782, 353565]], ![![-520620677314, -57755935995, 5324758372], ![184349510489, 157294054188, -195455]]], ![![![-813903189563, -90291727937, 8324367454], ![288199568502, 245902896252, -305550]], ![![2887426008852, 320321491528, -29531761758], ![-1022424952238, -872372079854, 1083975]]]]
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
  ![![81, 0, 0], ![-99, 16, 3]] ![![1458, 0, 0], ![-173, 633, 1]]
  ![![1458, 0, 0], ![-15795, -891, 567]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![118098, 0, 0], ![-14013, 51273, 81]], ![![-144342, 23328, 4374], ![401841, 23409, 29889]]]
 hmul := by decide
 f := ![![![![67449073698081315, 131872567443720381, 581519737541722053], ![49648947311144574, -446501016978353388, -37566285615]], ![![27496, 0, 0], ![0, 0, 0]]], ![![![-745374071328634172, -1457312711692317009, -6426325975500570095], ![-548666363605543610, 4934245388858441969, 415141879915]], ![![-303856, 0, 0], ![0, 0, 0]]]]
 g := ![![![![111069234, 17515200, 152473890], ![-1154656269, -160775847, 352836]], ![![-13179020, -2078273, -18092202], ![137008821, 19077286, -41866]]], ![![![-135750972, -21407446, -186357125], ![1411247619, 196503957, -431244]], ![![377924185, 59597294, 518808525], ![-3928839728, -547056767, 1200562]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1458, 0, 0], ![-15795, -891, 567]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
