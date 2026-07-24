import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_561295_1.RI3_1_561295_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-104, -31, -17]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-17, -5, -2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![2, -1, 9]]]
 hmul := by decide
 f := ![![![![-370454, -70007, 8809], ![-146820, 0, -15813]], ![![0, 0, 0], ![17910, 0, 18]]], ![![![123437, 23326, -2935], ![48924, 0, 5269]], ![![0, 0, 0], ![-5968, 0, -6]]]]
 g := ![![![![2127, 687, -56], ![-387, 0, 252]], ![![532, 172, -14], ![-96, 0, 63]]], ![![![532, 172, -14], ![-96, 0, 63]], ![![533, 171, -13], ![-91, 0, 63]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-2, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![27, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![-6, 3, 0], ![-1, -4, 9]]]
 hmul := by decide
 f := ![![![![-249157341, -47268243, 17710801], ![-98808525, 0, -10625742]], ![![-10955088, 0, 17334], ![-14067, 0, 54]]], ![![![27669775, 5249300, -1966845], ![10973025, 0, 1180025]], ![![1216600, 0, -1925], ![1562, 0, -6]]]]
 g := ![![![![-77497, 406124, -731306], ![20790, 2193750, 756]], ![![-19376, 101542, -182846], ![5202, 548496, 189]]], ![![![19375, -101528, 182820], ![-5178, -548418, -189]], ![![1, -5, 9], ![1, -26, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-2, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![81, 0, 0], ![-29, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![27, 27, 0]], ![![-6, 3, 0], ![-1, -4, 9]]]
 hmul := by decide
 f := ![![![![-18276533099, -3469795631, 1298745403], ![-7248776241, 0, -779301972]], ![![-2362190850, 0, 1300050], ![-42201, 0, 162]]], ![![![6768734874, 1285042768, -480991841], ![2684592549, 0, 288615374]], ![![874840075, 0, -481475], ![15629, 0, -60]]]]
 g := ![![![![51904, -2098391, 591208], ![-44469, -5314572, 2268]], ![![13005, -524673, 147823], ![-11043, -1328832, 567]]], ![![![-4306, 174857, -49265], ![3759, 442860, -189]], ![![0, 11, -3], ![1, 28, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-29, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![243, 0, 0], ![-29, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![81, 81, 0]], ![![-87, 3, 0], ![-28, -31, 9]]]
 hmul := by decide
 f := ![![![![42772844276397, 8226423339525, -3022397870690], ![16999755871977, 0, 1818232680888]], ![![1558056417372, -70162884936, 628847550], ![910764, 0, -243]]], ![![![-5280504534244, -1015589832284, 373128930995], ![-2098698122176, 0, -224469194840]], ![![-192349237366, 8661931146, -77634125], ![-112438, 0, 30]]]]
 g := ![![![![-77395, 2625041, -737435], ![20169, 19929645, 6804]], ![![-19354, 656354, -184385], ![5022, 4983120, 1701]]], ![![![27977, -947929, 266295], ![-7041, -7196790, -2457]], ![![6472, -218790, 61463], ![-1502, -1661075, -567]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-29, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![729, 0, 0], ![-29, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![243, 243, 0]], ![![-87, 3, 0], ![-28, -31, 9]]]
 hmul := by decide
 f := ![![![![-515595883145489, -99746235197081, 36641917142710], ![-205114039447521, 0, -21886823576232]], ![![-63959353812648, -4419462446208, 1886542650], ![2732292, 0, -729]]], ![![![21217561787484, 4104710641698, -1507871118451], ![8440757476394, 0, 900676376094]], ![![2632025556776, 181867661448, -77634125], ![-112438, 0, 30]]]]
 g := ![![![![-675050, 21745366, -6115025], ![56862, 495373725, 20412]], ![![-168783, 5437155, -1528985], ![14337, 123861960, 5103]]], ![![![81264, -2617488, 736065], ![-6636, -59628090, -2457]], ![![18762, -604142, 169891], ![-1394, -13762745, -567]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0, 0], ![-29, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![2187, 0, 0], ![-758, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![729, 729, 0]], ![![-87, 3, 0], ![-28, -31, 9]]]
 hmul := by decide
 f := ![![![![30967040293441641, 5969005280491905, -2193014499543434], ![12312015191311185, 0, 1315686053313144]], ![![10675276750029096, 16572984173280, 5659627950], ![8196876, 0, -2187]]], ![![![-10747127173763630, -2071546335795582, 761086803813549], ![-4272891169853068, 0, -456609517787792]], ![![-3704860256599420, -5751662634570, -1964176775], ![-2844730, 0, 759]]]]
 g := ![![![![815517354, -790494170712, 9348838711], ![-644104305, -2271762676557, 61236]], ![![203910360, -197653254834, 2337561070], ![-161049222, -568026057456, 15309]]], ![![![-32721126, 31717236429, -375106280], ![25843947, 91150620198, -2457]], ![![-7552072, 7320653949, -86578264], ![5965876, 21038470651, -567]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0, 0], ![-758, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6561, 0, 0], ![-758, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![2187, 2187, 0]], ![![-2274, 3, 0], ![-757, -760, 9]]]
 hmul := by decide
 f := ![![![![7707819306432194184456392, 1487865228394693133912594, -545609363736637244504855], ![3065228178275629106122998, 0, 327366004107236897397042]], ![![314269744478765659812576, -156274191556454823516, 14759723522925], ![780299730, 0, -6561]]], ![![![-891668148755196619970402, -172121579535836343268902, 63118045709836569770715], ![-354596576097010987746434, 0, -37870872064176856668500]], ![![-36355849836191899842940, 18078358293515721120, -1707457690250], ![-90267868, 0, 759]]]]
 g := ![![![![-86420671, 67551395372, -798878468], ![20286612, 582397793820, 183708]], ![![-21608002, 16890390329, -199749674], ![5076027, 145621360008, 45927]]], ![![![29963595, -23420593470, 276977370], ![-7025934, -201921838788, -63693]], ![![7469883, -5838658096, 69049325], ![-1750832, -50338287980, -15876]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![6561, 0, 0], ![-758, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![19683, 0, 0], ![-758, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![19683, 0, 0], ![6561, 6561, 0]], ![![-2274, 3, 0], ![-757, -760, 9]]]
 hmul := by decide
 f := ![![![![-7237642776214216852902779, -1397526274933725103871741, 512297863717340416452523], ![-2878389683715980652258171, 0, -307374552698973249949002]], ![![-890757204075328292445600, -5061116979055176955650, 44279170568775], ![2340899190, 0, -19683]]], ![![![279092147815523207927063, 53890281927384326358903, -19754817352420395331715], ![110994143247635844761991, 0, 11852729783586256924640]], ![![34348661429456494809920, 195162714119052645000, -1707457690250], ![-90267868, 0, 759]]]]
 g := ![![![![-365161079, 278716450114, -3296231264], ![28225422, 7208903946312, 551124]], ![![-91303932, 69689605704, -824181914], ![7059636, 1802497388904, 137781]]], ![![![42201895, -32211052709, 380942994], ![-3248985, -833127663936, -63693]], ![![10520771, -8030084421, 94967539], ![-809693, -207695337848, -15876]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![19683, 0, 0], ![-758, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![59049, 0, 0], ![18925, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![59049, 0, 0], ![19683, 19683, 0]], ![![-2274, 3, 0], ![-757, -760, 9]]]
 hmul := by decide
 f := ![![![![2708520337607171747171288, 522857751532497038735186, -191724980751476236351703], ![1077126029713222928635494, 0, 115034872951298668865058]], ![![994815031428588601979856, 421007123710074726612, 132837511706325], ![7022697570, 0, -59049]]], ![![![868025519728008091257233, 167565244098838228173739, -61443945519222985108626], ![345196921275615439810327, 0, 36866330296272098057026]], ![![318817925307480564845732, 134924195433762863844, 42571712878525], ![2250631322, 0, -18924]]]]
 g := ![![![![7280780887, 169306092096898, 80527682104], ![5200681626, -528345599693076, 1653372]], ![![1820453228, 42332897095448, 20134952269], ![1300416444, -132106291189092, 413343]]], ![![![-280496528, -6522193019879, -3102174763], ![-200288937, 20353502580576, -63693]], ![![-69923621, -1625956190644, -773359551], ![-49940648, 5074045404868, -15876]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![59049, 0, 0], ![18925, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![177147, 0, 0], ![-40124, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![177147, 0, 0], ![59049, 59049, 0]], ![![56775, 3, 0], ![18926, 18923, 9]]]
 hmul := by decide
 f := ![![![![-2884621857831059816628130773034951, -556877755688637952769755430241925, 204188079477915162071329792552324], ![-1147166537839899256465962067758957, 0, -122512847481180098097809228568054]], ![![127424320677597037358594724247728, -2247897532981868070421755222, 250725487691968875], ![-529844374089, 0, 354294]]], ![![![653386464600060114293006366083163, 126136598118062484250285994896608, -46249988365499155717059180104014], ![259841020906040866181097453659927, 0, 27749992972736717370669493220345]], ![![-28862475046972169380655493076482, 509164075655505927846661246, -56791027754104925], ![120013353374, 0, -80250]]]]
 g := ![![![![-647498520831, 28792370975224020, -6457778894900], ![309193082388, 127108484099411580, 4960116]], ![![-161899009160, 7199176725020338, -1614687847580], ![77309903250, 31781906431690860, 1240029]]], ![![![-207518283076, 9227733337826456, -2069668442660], ![99094049088, 40737291043312500, 1589679]], ![![-51893548499, 2307554971947621, -517556536413], ![24780196657, 10187067078036640, 397467]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![177147, 0, 0], ![-40124, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-104, -31, -17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![531441, 0, 0], ![177147, 177147, 0]], ![![-120372, 3, 0], ![-40123, -40126, 9]]]
 hmul := by decide
 f := ![![![![-31591040241024805973655483317421, -6098650905763720583963212454913, 2236174503720724943277381077590], ![-12563230382262842185872898590777, 0, -1341704701855846599457487940132]], ![![-1974500104187739836173498743108, -12353983432393866843901656, -464147871488550], ![-462729396, 0, 73]]]]
 g := ![![![![402052, -14140, 17217]], ![![-324077, 11447, -13725]]], ![![![-91073, 3203, -3900]], ![![73410, -2593, 3109]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow12 : J0 ^ 12 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-8241, 291, -353])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-29, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-29, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-29, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![-758, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![-758, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     

lemma PowJ0_9 : J0 ^ 9 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19683, 0, 0], ![-758, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     

lemma PowJ0_10 : J0 ^ 10 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![59049, 0, 0], ![18925, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     

lemma PowJ0_11 : J0 ^ 11 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![177147, 0, 0], ![-40124, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     
