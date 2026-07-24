import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_325983_1.RI3_1_325983_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![282, -63, 8]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-5, 0, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![0, 1, 5]]]
 hmul := by decide
 f := ![![![![1401, 1680, 390], ![-5366, 326, 0]], ![![0, 0, 0], ![-1656, -24, 0]]], ![![![-467, -562, -135], ![1792, -106, 0]], ![![0, 0, 0], ![553, 8, 0]]]]
 g := ![![![![4, 15, -40], ![9, 72, 0]], ![![1, -8, 20], ![3, -36, 0]]], ![![![1, -8, 20], ![3, -36, 0]], ![![1, -4, 10], ![3, -17, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![27, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![0, -2, 5]]]
 hmul := by decide
 f := ![![![![0, -17094, -13900], ![73015, -1420, 0]], ![![-4203, 25776, 0], ![10368, -72, 0]]], ![![![0, 1894, 1540], ![-8092, 158, 0]], ![![467, -2856, 0], ![-1154, 8, 0]]]]
 g := ![![![![4, 159, -400], ![27, 2160, 0]], ![![1, -20, 50], ![9, -270, 0]]], ![![![0, -60, 150], ![3, -810, 0]], ![![3, 3, -10], ![27, 55, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![81, 0, 0], ![24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![0, 27, 0]], ![![-9, 3, 0], ![0, -2, 5]]]
 hmul := by decide
 f := ![![![![0, -394100, -306150], ![1657027, -35518, 0]], ![![-12609, 1962360, 0], ![31104, -216, 0]]], ![![![0, -116776, -90715], ![490993, -10524, 0]], ![![-3736, 581463, 0], ![9214, -64, 0]]]]
 g := ![![![![-47, 11048, 2210], ![162, -35802, 0]], ![![-8, -650, -130], ![27, 2106, 0]]], ![![![-1, -1300, -260], ![3, 4212, 0]], ![![-16, 49, 10], ![54, -161, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![24, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![243, 0, 0], ![-57, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![0, 81, 0]], ![![72, 3, 0], ![0, 25, 5]]]
 hmul := by decide
 f := ![![![![-2610063, 4830491, 5477810], ![1610164, -2738905, 0]], ![![8813691, -14804127, 0], ![58320, -648, 0]]], ![![![612237, -1133152, -1285000], ![-377716, 642500, 0]], ![![-2067409, 3472794, 0], ![-13682, 152, 0]]]]
 g := ![![![![172, 129469, -11560], ![729, 561816, 0]], ![![19, -7616, 680], ![81, -33048, 0]]], ![![![58, 38079, -3400], ![246, 165240, 0]], ![![19, -2352, 210], ![81, -10205, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-57, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![729, 0, 0], ![186, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![0, 243, 0]], ![![-171, 3, 0], ![0, -56, 5]]]
 hmul := by decide
 f := ![![![![-18951327, 286282543, -186922300], ![95427517, 93461150, 0]], ![![-80798472, 1514115990, 0], ![-244944, -1944, 0]]], ![![![-4835318, 73042457, -47691570], ![24347487, 23845785, 0]], ![![-20615248, 386313290, 0], ![-62495, -496, 0]]]]
 g := ![![![![-185, 476475, 12740], ![729, -1857492, 0]], ![![-62, -4862, -130], ![243, 18954, 0]]], ![![![-1, -111826, -2990], ![3, 435942, 0]], ![![-124, 1121, 30], ![486, -4373, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0, 0], ![186, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![2187, 0, 0], ![-543, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![0, 729, 0]], ![![558, 3, 0], ![0, 187, 5]]]
 hmul := by decide
 f := ![![![![-8511075, -159950895, -27747580], ![-53316965, 13873790, 0]], ![![33363414, 675084618, 0], ![-1364688, -5832, 0]]], ![![![2113175, 39713074, 6889250], ![13237693, -3444625, 0]], ![![-8283646, -167611977, 0], ![338830, 1448, 0]]]]
 g := ![![![![15748, 145602851, -1343200], ![63423, 587515680, 0]], ![![181, -249320, 2300], ![729, -1006020, 0]]], ![![![4345, 37148672, -342700], ![17499, 149896980, 0]], ![![181, -63956, 590], ![729, -258065, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0, 0], ![-543, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![6561, 0, 0], ![-543, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![0, 2187, 0]], ![![-1629, 3, 0], ![0, -542, 5]]]
 hmul := by decide
 f := ![![![![-36767844, 128821873961, -7996432000], ![42940624654, 3998216000, 0]], ![![-148092705, 582940301040, 0], ![-10707552, -17496, 0]]], ![![![3042972, -10661536035, 661799470], ![-3553845342, -330899735, 0]], ![![12256415, -48245215150, 0], ![886177, 1448, 0]]]]
 g := ![![![![6517, 509111428, -4696600], ![78732, 6162878520, 0]], ![![181, -249320, 2300], ![2187, -3018060, 0]]], ![![![-1086, -126405238, 1166100], ![-13119, -1530156420, 0]], ![![543, 61787, -570], ![6561, 747955, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![6561, 0, 0], ![-543, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![19683, 0, 0], ![-543, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![19683, 0, 0], ![0, 6561, 0]], ![![-1629, 3, 0], ![0, -542, 5]]]
 hmul := by decide
 f := ![![![![-36767844, 204508480835, -12694545400], ![68169493612, 6347272700, 0]], ![![-444278115, 2776298303700, 0], ![-32122656, -52488, 0]]], ![![![1014324, -5641831299, 350207890], ![-1880610432, -175103945, 0]], ![![12256415, -76590499330, 0], ![886177, 1448, 0]]]]
 g := ![![![![2716, 1599637115, -14756800], ![98415, 58091618880, 0]], ![![181, -249320, 2300], ![6561, -9054180, 0]]], ![![![0, -132388920, 1221300], ![3, -4807769580, 0]], ![![543, 20595, -190], ![19683, 747955, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![19683, 0, 0], ![-543, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![59049, 0, 0], ![-543, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![59049, 0, 0], ![0, 19683, 0]], ![![-1629, 3, 0], ![0, -542, 5]]]
 hmul := by decide
 f := ![![![![1487263907684, 2157841507285, -1926304765970], ![-8224196312989, 1155782860111, -42491858526]], ![![1771030413, 203391, 0], ![-96367968, -157464, 0]]], ![![![-13676514547, -19842981935, 17713826770], ![75627694842, -10628296067, 390744723]], ![![-16283935, -982, 0], ![886177, 1448, 0]]]]
 g := ![![![![7603, 47231024690, -435710560], ![826686, 5145654571488, 0]], ![![181, -7361444, 67910], ![19683, -802003518, 0]]], ![![![0, -1302975588, 12020070], ![3, -141954622686, 0]], ![![543, 202707, -1870], ![59049, 22084327, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![59049, 0, 0], ![-543, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![177147, 0, 0], ![58506, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![177147, 0, 0], ![0, 59049, 0]], ![![-1629, 3, 0], ![0, -542, 5]]]
 hmul := by decide
 f := ![![![![44064377266721, 63713079412875, -56876672786670], ![-242873901537715, 34126003672889, -1257744098361]], ![![4712373656955, -6436341, 0], ![-289103904, -472392, 0]]], ![![![14553057349373, 21042396513735, -18784549611930], ![-80213497543897, 11270729767451, -415392730575]], ![![1556346639950, -2126746, 0], ![-95481791, -156016, 0]]]]
 g := ![![![![-41129717, 24456066416097, 2090012000], ![124534341, -74047871152800, 0]], ![![-19502, -3811731050, -325750], ![59049, 11541127050, 0]]], ![![![351035, -224892131944, -19219250], ![-1062879, 680926495950, 0]], ![![-39004, 34987185, 2990], ![118098, -105933905, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![177147, 0, 0], ![58506, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![531441, 0, 0], ![-118641, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![531441, 0, 0], ![0, 177147, 0]], ![![175518, 3, 0], ![0, 58507, 5]]]
 hmul := by decide
 f := ![![![![-175299888231, -144660413265220512168, -82410681146319040], ![-48220137755073504056, 41205340573159520, 0]], ![![530780595984, 486626831183747880648, 0], ![-165631027824, -1417176, 0]]], ![![![39134643431, 32294565321965305954, 18397687836187850], ![10764855107321768653, -9198843918093925, 0]], ![![-118493568784, -108636506922401081883, 0], ![36976128622, 316376, 0]]]]
 g := ![![![![1011058603, 2526749831835638, -106488108220], ![4528940202, 11318429344109004, 0]], ![![39547, -20292897440, 855230], ![177147, -90900857286, 0]]], ![![![333974416, 834504821422305, -35169623290], ![1496006418, 3738115954172178, 0]], ![![39547, -6702210880, 282460], ![177147, -30022164971, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ011 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![531441, 0, 0], ![-118641, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![1594323, 0, 0], ![-118641, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := rfl
 M := ![![![1594323, 0, 0], ![0, 531441, 0]], ![![-355923, 3, 0], ![0, -118640, 5]]]
 hmul := by decide
 f := ![![![![-2916149627250, 343479631218991702536, -96508796238533020], ![114493210406330567515, 48254398119266510, 0]], ![![-13062613049451, 1709624372726840091714, 0], ![-504698888880, -4251528, 0]]], ![![![217004275750, -25559919118356666285, 7181669018661960], ![-8519973039452222095, -3590834509330980, 0]], ![![972049876217, -127221112164898404919, 0], ![37556994961, 316376, 0]]]]
 g := ![![![![872723197, 18801425326746244, -792372948700], ![11727839988, 252659683338046020, 0]], ![![39547, -62326337600, 2626700], ![531441, -837561644820, 0]]], ![![![-194808522, -4197304879332758, 176892484800], ![-2617878363, -56404751408758080, 0]], ![![118641, 13913861919, -586390], ![1594323, 186979012795, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ012 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![1594323, 0, 0], ![-118641, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![4782969, 0, 0], ![-118641, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := rfl
 M := ![![![4782969, 0, 0], ![0, 1594323, 0]], ![![-355923, 3, 0], ![0, -118640, 5]]]
 hmul := by decide
 f := ![![![![-12731040632259, 1057262036253446060445, -297062990485419100], ![352420678751148686815, 148531495242709550, 0]], ![![-171082432684980, 15787145272656458799270, 0], ![-1514096666640, -12754584, 0]]], ![![![315792009451, -26225264108229106311, 7368613565154930], ![-8741754702743035435, -3684306782577465, 0]], ![![4243680211220, -391598336167957497520, 0], ![37556994961, 316376, 0]]]]
 g := ![![![![813639979, 156978625699757302, -6615754623220], ![32801601402, 6328589854893588036, 0]], ![![39547, -188426658080, 7941110], ![1594323, -7596416591118, 0]]], ![![![-60506910, -11681510667669090, 492309114450], ![-2439314187, -470939846566360410, 0]], ![![118641, 14021587039, -590930], ![4782969, 565279974235, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ013 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![4782969, 0, 0], ![-118641, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![282, -63, 8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012
 hI2 := rfl
 M := ![![![14348907, 0, 0], ![0, 4782969, 0]], ![![-355923, 3, 0], ![0, -118640, 5]]]
 hmul := by decide
 f := ![![![![217886471152963930, 316157702483900760, -294046475955651966], ![-1212055578535260014, 176427885573391179, -6225327536274144]], ![![297657846076, 974162, 0], ![-89269983, -752, 0]]]]
 g := ![![![![-348940, -19110, -18989]], ![![-664615, -34068, -31850]]], ![![![8655, 474, 471]], ![![16485, 845, 790]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow15 : J0 ^ 15 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ013, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![361, 21, 19])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-57, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![186, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![-543, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![-543, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     

lemma PowJ0_9 : J0 ^ 9 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19683, 0, 0], ![-543, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     

lemma PowJ0_10 : J0 ^ 10 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![59049, 0, 0], ![-543, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     

lemma PowJ0_11 : J0 ^ 11 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![177147, 0, 0], ![58506, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     

lemma PowJ0_12 : J0 ^ 12 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![531441, 0, 0], ![-118641, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010]
 rfl     

lemma PowJ0_13 : J0 ^ 13 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1594323, 0, 0], ![-118641, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011]
 rfl     

lemma PowJ0_14 : J0 ^ 14 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4782969, 0, 0], ![-118641, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012]
 rfl     
