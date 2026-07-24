import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-218, -9, -13]

def alpha1 := B.equivFun.symm ![-74, -3, -4]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-31, 9, -6]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![169, 0, 0], ![69, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![52, 13, 0], ![11, 6, 13]]]
 hmul := by decide
 f := ![![![![-21620440681, 1516597522, -782210902], ![-6535781928, 0, 1659638812]], ![![0, 0, 0], ![210811614, 0, -18590]]], ![![![-8814487417, 618305148, -318901370], ![-2664588036, 0, 676621982]], ![![0, 0, 0], ![85946274, 0, -7579]]]]
 g := ![![![![5037496, -76270923, -14796267], ![1605500, 192360701, -1690]], ![![1511257, -22881529, -4438929], ![481676, 57708846, -507]]], ![![![1511257, -22881529, -4438929], ![481676, 57708846, -507]], ![![309977, -4693712, -910562], ![98877, 11837875, -104]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![169, 0, 0], ![69, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![-218, -9, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![676, 169, 0]], ![![897, 13, 0], ![271, 71, 13]]]
 hmul := by decide
 f := ![![![![-182020956567174232, 12829336146498149, -6449141903891093], ![-55019576163246053, 0, 13972710701454396]], ![![262361298222369, 0, 472460808873], ![2326130331, 0, 23881]]]]
 g := ![![![![-49, 44, -39]], ![![-587, 27, 26]]], ![![![-64, 19, -13]], ![![-212, 6, 13]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![19, 0, 0], ![-9, 1, 0]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![361, 0, 0], ![48, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![361, 0, 0], ![-171, 19, 0]], ![![-171, 19, 0], ![76, -20, 13]]]
 hmul := by decide
 f := ![![![![-1947895, -4577567, 5394454], ![681777, -7942000, 0]], ![![0, 0, 0], ![1013688, -4693, 0]]], ![![![-259037, -608746, 717379], ![90672, -1056163, 0]], ![![0, 0, 0], ![134802, -624, 0]]]]
 g := ![![![![162864, -1520027, -429559], ![17689, 11928523, 0]], ![![-77257, 720474, 203606], ![-7923, -5653982, 0]]], ![![![-77257, 720474, 203606], ![-7923, -5653982, 0]], ![![34316, -320493, -90571], ![3905, 2515088, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![361, 0, 0], ![48, 1, 0]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![-74, -3, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![6859, 0, 0], ![-3249, 361, 0]], ![![912, 19, 0], ![-437, 37, 13]]]
 hmul := by decide
 f := ![![![![-69989460864, -164475233050, 192677150074], ![24496311322, -281603557489, 0]], ![![56303537753, -28622908, 0], ![-591627, 962, 0]]]]
 g := ![![![![-556, 44, 3]], ![![281, -56, 29]]], ![![![-73, 4, 2]], ![![53, -7, 2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-15721, -639, -939])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![361, 0, 0], ![48, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![13, 0, 0], ![4, 1, 0]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![247, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![247, 0, 0], ![-117, 13, 0]], ![![76, 19, 0], ![-41, -7, 13]]]
 hmul := by decide
 f := ![![![![1724063859, 4051550067, -4689894799], ![-603422349, 6854479957, 0]], ![![-668519579, 0, -27170], ![0, 0, 0]]], ![![![-63518139, -149267630, 172785593], ![22231352, -252533465, 0]], ![![24629668, 0, 1001], ![0, 0, 0]]]]
 g := ![![![![32918368, 72492531, -85668822], ![-905749, 1627706288, -2470]], ![![-15766073, -34719912, 41030626], ![433914, -779581257, 1183]]], ![![![9875639, 21748045, -25700984], ![-271757, 488318297, -741]], ![![-5370930, -11827835, 13977669], ![148039, -265575493, 403]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![247, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![13, 0, 0], ![4, 1, 0]] ![![361, 0, 0], ![48, 1, 0]]
  ![![4693, 0, 0], ![2214, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4693, 0, 0], ![624, 13, 0]], ![![1444, 361, 0], ![187, 50, 13]]]
 hmul := by decide
 f := ![![![![178314058294573496, -1663906471617528124, -470219488326409255], ![19100189270144206, 13057633483528078315, 0]], ![![-150442618716, 0, -187720], ![0, 0, 0]]], ![![![84118792598557653, -784939811970238913, -221823764164380859], ![9010421697397828, 6159875297181249607, 0]], ![![-70970576088, 0, -88556], ![0, 0, 0]]]]
 g := ![![![![11717703089, -6067811434727, -35660708816], ![4235071139, 12873523882336, -46930]], ![![1554787658, -805120484049, -4731717103], ![561940990, 1708150935647, -6227]]], ![![![3515357518, -1820368585661, -10698360483], ![1270543110, 3862110534291, -14079]], ![![454432581, -235320271048, -1382984253], ![164244066, 499257625574, -1820]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4693, 0, 0], ![2214, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![69, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![169, 0, 0], ![69, 1, 0]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![3211, 0, 0], ![238, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![3211, 0, 0], ![-1521, 169, 0]], ![![1311, 19, 0], ![-626, 58, 13]]]
 hmul := by decide
 f := ![![![![9442466896754067, 22189797207372046, -26001918366612037], ![-3304863413863912, 38002715301810077, 0]], ![![-2466887317905153, 786872838024, -353210], ![0, 0, 0]]], ![![![699583580404806, 1644021413951278, -1926457921135093], ![-244854253141666, 2815585792001428, 0]], ![![-182769384440049, 58298675904, -26169], ![0, 0, 0]]]]
 g := ![![![![5486301468, -260092710196, -14327132825], ![325646776, 3538802400575, -32110]], ![![-2627634205, 124569982618, 6861901995], ![-155965537, -1694890076685, 15379]]], ![![![2236724599, -106037880033, -5841066405], ![132764514, 1442743643715, -13091]], ![![-1079485612, 51175883745, 2819008973], ![-64073673, -696295332970, 6318]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3211, 0, 0], ![238, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![169, 0, 0], ![69, 1, 0]] ![![361, 0, 0], ![48, 1, 0]]
  ![![61009, 0, 0], ![16293, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![61009, 0, 0], ![8112, 169, 0]], ![![24909, 361, 0], ![3307, 115, 13]]]
 hmul := by decide
 f := ![![![![3009335165517172935866242, -28081091990747729396003629, -7935708431608098060420441], ![322346249180267511151325, 220368518754653019414373411, 0]], ![![-142065258040062656, 1229698990234, -2440360], ![0, 0, 0]]], ![![![803664982516421016991605, -7499261153221485479912826, -2119289021383464959591568], ![86084925228716685140683, 58851025901493979314830060, 0]], ![![-37939566993806912, 328400116016, -651716], ![0, 0, 0]]]]
 g := ![![![![-8862863016, 30501466515593, 24339925046], ![-1866936409, -114226503516528, -610090]], ![![-1175997767, 4047152055571, 3229594801], ![-247681330, -15156386932128, -80951]]], ![![![-3613329647, 12435223011176, 9923207983], ![-761114711, -46569303291984, -248729]], ![![-478758536, 1647589244013, 1314762970], ![-100786898, -6170141310384, -32955]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![61009, 0, 0], ![16293, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
