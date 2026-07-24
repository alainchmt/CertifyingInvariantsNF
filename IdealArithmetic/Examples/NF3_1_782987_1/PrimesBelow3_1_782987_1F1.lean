
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [30, 9, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 6, 32], [1, 30, 5], [0, 1]]
 g := ![![[33, 4, 12], [6, 1], [22, 31, 30], [10, 1], []], ![[6, 4, 3, 29], [3, 9], [36, 31], [7, 12], [5, 25]], ![[9, 22, 6, 19], [28, 16], [22, 20, 5, 2], [20, 36], [32, 25]]]
 h' := ![![[9, 6, 32], [4, 3, 30], [6, 35, 1], [33, 28, 17], [0, 0, 1], [0, 1]], ![[1, 30, 5], [33, 17, 34], [30, 4, 3], [0, 33], [5, 16, 30], [9, 6, 32]], ![[0, 1], [23, 17, 10], [7, 35, 33], [1, 13, 20], [3, 21, 6], [1, 30, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 15], []]
 b := ![[], [10, 21, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [30, 9, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47878, -24901, -1813]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1294, -673, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [21, 16, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 12, 33], [3, 28, 8], [0, 1]]
 g := ![![[34, 18, 20], [38, 31], [20, 31], [16, 27, 1], []], ![[9, 4, 16, 32], [13, 18], [31, 18], [3, 23, 28, 1], [19, 23]], ![[7, 16, 18, 20], [6, 18], [0, 39], [10, 18, 3, 4], [3, 23]]]
 h' := ![![[24, 12, 33], [27, 40, 15], [13, 20, 20], [33, 38, 20], [0, 0, 1], [0, 1]], ![[3, 28, 8], [34, 21, 18], [15, 38, 31], [16, 8, 10], [13, 35, 28], [24, 12, 33]], ![[0, 1], [34, 21, 8], [18, 24, 31], [10, 36, 11], [28, 6, 12], [3, 28, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 26], []]
 b := ![[], [31, 9, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [21, 16, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![379742, 262646, 45264]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9262, 6406, 1104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![118423354797263646976985183, -7762915032706746641125420, 2334147509757258551974719]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![118423354797263646976985183, -7762915032706746641125420, 2334147509757258551974719]] 
 ![![43, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![118423354797263646976985183, -7762915032706746641125420, 2334147509757258551974719], ![-275429406151356509133016842, 18055011877701529242072266, -5428767522949488089150701], ![640594567708039594519782718, -41992402664528521299536699, 12626244354752041152921565]]]
  hmulB := by decide  
  f := ![![![-21378931259709, -7013673030281, 936618876166]], ![![-16491420992080, -6000846227505, 468564520431]], ![![269480432911, -1875788575812, -856329631988]]]
  g := ![![![6017630416071233039844912, -7762915032706746641125420, 2334147509757258551974719], ![-13995823499294563278350399, 18055011877701529242072266, -5428767522949488089150701], ![32551529735070251926986015, -41992402664528521299536699, 12626244354752041152921565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5769227469, -378185728, 113712603]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![5769227469, -378185728, 113712603]] 
 ![![43, 0, 0], ![29, 1, 0], ![19, 0, 1]] where
  M :=![![![5769227469, -378185728, 113712603], ![-13418087154, 879585540, -264473125], ![31207828750, -2045742779, 615112415]]]
  hmulB := by decide  
  f := ![![![164725, 69383, -620]], ![![112795, 51244, 1181]], ![![-115913, -36404, 5776]]]
  g := ![![![338978468, -378185728, 113712603], ![-788397173, 879585540, -264473125], ![1833656592, -2045742779, 615112415]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![118423354797263646976985183, -7762915032706746641125420, 2334147509757258551974719]] ![![118423354797263646976985183, -7762915032706746641125420, 2334147509757258551974719]]
  ![![17657468253880192523373979219463576989668124204973371, -1157486426408483968467712318241998597076799254966161, 348032156528339109744333717253507918544583345423232]] where
 M := ![![![17657468253880192523373979219463576989668124204973371, -1157486426408483968467712318241998597076799254966161, 348032156528339109744333717253507918544583345423232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![17657468253880192523373979219463576989668124204973371, -1157486426408483968467712318241998597076799254966161, 348032156528339109744333717253507918544583345423232]] ![![5769227469, -378185728, 113712603]]
  ![![43, 0, 0]] where
 M := ![![![128262532572831719093597760124833364511220199675604694533043793, -8407895080723393508841120297612836356792628493466523500002756, 2528079630175720509360838003305299901398165420205463363643118]]]
 hmul := by decide  
 g := ![![![![2982849594717016723106924654065892197935353480828016151931251, -195532443737753337414909774363089217599828569615500546511692, 58792549538970244403740418681518602358096870237336357294026]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -4, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![55, -4, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![8, 43, 1]] where
  M :=![![![55, -4, 1], ![-118, 12, -3], ![354, 11, 9]]]
  hmulB := by decide  
  f := ![![![3, 1, 0]], ![![0, 3, 1]], ![![-2, 2, 1]]]
  g := ![![![1, -1, 1], ![-2, 3, -3], ![6, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [26, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 46], [0, 1]]
 g := ![![[12, 21], [28, 42], [40, 34], [34, 7], [1]], ![[40, 26], [37, 5], [7, 13], [12, 40], [1]]]
 h' := ![![[17, 46], [24, 31], [41, 18], [9, 38], [21, 17], [0, 1]], ![[0, 1], [34, 16], [18, 29], [44, 9], [28, 30], [17, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [10, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [26, 30, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2320, -173, 55]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, -54, 55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![38, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![-118, -43, 4]]]
  hmulB := by decide  
  f := ![![![55, -4, 1]], ![![1, 0, 0]], ![![52, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-3, -43, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![55, -4, 1]] ![![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![360633578539805730169486032973, -23640335413046205871167063906, 7108158443278510251610266009]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![360633578539805730169486032973, -23640335413046205871167063906, 7108158443278510251610266009]] 
 ![![53, 0, 0], ![0, 53, 0], ![49, 2, 1]] where
  M :=![![![360633578539805730169486032973, -23640335413046205871167063906, 7108158443278510251610266009], ![-838762696306864209690011389062, 54982765478829789350244594586, -16532176969767695619556797897], ![1950796882432588083107702151846, -127879086606853298049069079491, 38450588509062093730687796689]]]
  hmulB := by decide  
  f := ![![![168359982707459, 51716096639355, -8888024449464]], ![![1048786885036752, 550545034034411, 42828072189891]], ![![99877366119469, 53629407250352, 4594642501516]]]
  g := ![![![232713487153938261143075444, -714276458483079742912973508, 7108158443278510251610266009], ![-541245750721643855315628153, 1661266404120097746969022460, -16532176969767695619556797897], ![1258831046953688496301888945, -3863778558961839349253673073, 38450588509062093730687796689]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [26, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52], [0, 1]]
 g := ![![[34, 43], [16], [3, 43], [4], [17, 1]], ![[23, 10], [16], [45, 10], [4], [34, 52]]]
 h' := ![![[17, 52], [50, 19], [28, 4], [8, 34], [35, 51], [0, 1]], ![[0, 1], [2, 34], [43, 49], [3, 19], [1, 2], [17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [19, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [26, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291, -1153, -497]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![454, -3, -497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-168359982707459, -51716096639355, 8888024449464]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-168359982707459, -51716096639355, 8888024449464]] 
 ![![53, 0, 0], ![50, 1, 0], ![44, 0, 1]] where
  M :=![![![-168359982707459, -51716096639355, 8888024449464], ![-1048786885036752, -550545034034411, -42828072189891], ![5053712518407138, 792820219128561, -593373106224302]]]
  hmulB := by decide  
  f := ![![![-360633578539805730169486032973, 23640335413046205871167063906, -7108158443278510251610266009]], ![![-324394645861951364128005476596, 21264792550443028381285067938, -6393881984795430508697292501]], ![![-336201402607246041708775237786, 22038751788318610497743771535, -6626595471949368769840367945]]]
  g := ![![![38233429688375, -51716096639355, 8888024449464], ![535149056472434, -550545034034411, -42828072189891], ![-159978901210408, 792820219128561, -593373106224302]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![360633578539805730169486032973, -23640335413046205871167063906, 7108158443278510251610266009]] ![![-168359982707459, -51716096639355, 8888024449464]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104335220686694943, -6839406420263270, 2056467628051441]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![104335220686694943, -6839406420263270, 2056467628051441]] 
 ![![59, 0, 0], ![0, 59, 0], ![43, 58, 1]] where
  M :=![![![104335220686694943, -6839406420263270, 2056467628051441], ![-242663180110070038, 15907112680482980, -4782938792211829], ![564386777480995822, -36996812044961391, 11124173888271151]]]
  hmulB := by decide  
  f := ![![![1390099, -14254079, -6385650]], ![![753506700, 275973049, -20639729]], ![![783027981, 288720788, -20616168]]]
  g := ![![![269612079330220, -2137534387241472, 2056467628051441], ![-627064610931549, 4971484112352018, -4782938792211829], ![1458428818395531, -11562693179062511, 11124173888271151]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [47, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[7, 5], [0, 21], [53], [58, 26], [25, 1]], ![[14, 54], [53, 38], [53], [0, 33], [50, 58]]]
 h' := ![![[25, 58], [0, 8], [13, 32], [47, 17], [5, 47], [0, 1]], ![[0, 1], [23, 51], [46, 27], [0, 42], [0, 12], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [33, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [47, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-307, -281, -73]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 67, -73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1390099, 14254079, 6385650]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1390099, 14254079, 6385650]] 
 ![![59, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-1390099, 14254079, 6385650], ![-753506700, -275973049, 20639729], ![-2435488022, -1641015047, -255333320]]]
  hmulB := by decide  
  f := ![![![-104335220686694943, 6839406420263270, -2056467628051441]], ![![4112935256102882, -269612079330220, 81066759190031]], ![![-9565877584423658, 627064610931549, -188545320140189]]]
  g := ![![![-23561, 14254079, 6385650], ![-12771300, -275973049, 20639729], ![-41279458, -1641015047, -255333320]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![104335220686694943, -6839406420263270, 2056467628051441]] ![![-1390099, 14254079, 6385650]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [29, 12, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 33, 57], [44, 27, 4], [0, 1]]
 g := ![![[10, 43, 9], [20, 15], [19, 42, 56], [10, 40, 4], [1]], ![[27, 49, 41, 47], [], [54, 41, 7, 34], [51, 20, 46, 39], [58, 2, 4, 58]], ![[57, 23, 20, 42], [58, 15], [44, 43, 22, 1], [60, 21, 7, 12], [36, 9, 9, 3]]]
 h' := ![![[15, 33, 57], [34, 0, 3], [59, 60, 36], [15, 49, 19], [32, 49, 59], [0, 1]], ![[44, 27, 4], [48, 34, 20], [29, 9], [5, 43, 12], [46, 49, 55], [15, 33, 57]], ![[0, 1], [21, 27, 38], [42, 53, 25], [35, 30, 30], [21, 24, 8], [44, 27, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 34], []]
 b := ![[], [1, 6, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [29, 12, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-653676, -368013, -46909]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10716, -6033, -769]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![164596328416571079, -10789656435428568, 3244225860232129]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![164596328416571079, -10789656435428568, 3244225860232129]] 
 ![![67, 0, 0], ![0, 67, 0], ![63, 62, 1]] where
  M :=![![![164596328416571079, -10789656435428568, 3244225860232129], ![-382818651507391222, 25094616426589532, -7545430575196439], ![890360807873179802, -58365136773944345, 17549185851393093]]]
  hmulB := by decide  
  f := ![![![57652463, 39749557, 6432772]], ![![-759067096, -218956733, 46182329]], ![![-729545815, -206208994, 46205890]]]
  g := ![![![-593879116090344, -3163159101042098, 3244225860232129], ![1381245891492305, 7356885255056250, -7545430575196439], ![-3212505981560971, -17110666560601733, 17549185851393093]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [59, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[31, 25], [46, 9], [10], [10], [65], [1]], ![[0, 42], [0, 58], [10], [10], [65], [1]]]
 h' := ![![[47, 66], [33, 5], [60, 3], [39, 55], [48, 55], [8, 47], [0, 1]], ![[0, 1], [0, 62], [0, 64], [11, 12], [20, 12], [6, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [44, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [59, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![630, 151, -57]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63, 55, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57652463, 39749557, 6432772]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![57652463, 39749557, 6432772]] 
 ![![67, 0, 0], ![4, 1, 0], ![51, 0, 1]] where
  M :=![![![57652463, 39749557, 6432772], ![-759067096, -218956733, 46182329], ![-5449514822, -2744907243, -172774404]]]
  hmulB := by decide  
  f := ![![![164596328416571079, -10789656435428568, 3244225860232129]], ![![4112935256102882, -269612079330220, 81066759190031]], ![![138578709807735893, -9084143507176139, 2731413503331816]]]
  g := ![![![-6409211, 39749557, 6432772], ![-33411029, -218956733, 46182329], ![214053862, -2744907243, -172774404]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![164596328416571079, -10789656435428568, 3244225860232129]] ![![57652463, 39749557, 6432772]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [67, 18, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 6, 21], [22, 64, 50], [0, 1]]
 g := ![![[41, 66, 19], [39, 25, 58], [67, 9, 1], [30, 1], [44, 1], []], ![[68, 21, 4, 33], [23, 47, 19, 47], [37, 70, 4, 51], [70, 2], [31, 49], [60, 15]], ![[12, 28, 6, 19], [12, 41, 65, 16], [40, 44, 66, 37], [30, 50], [6, 36], [31, 15]]]
 h' := ![![[22, 6, 21], [14, 9, 44], [55, 41, 22], [69, 53, 70], [34, 64, 1], [0, 0, 1], [0, 1]], ![[22, 64, 50], [47, 18, 23], [58, 15, 68], [14, 9, 55], [36, 54, 59], [14, 25, 64], [22, 6, 21]], ![[0, 1], [55, 44, 4], [62, 15, 52], [59, 9, 17], [62, 24, 11], [40, 46, 6], [22, 64, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 32], []]
 b := ![[], [43, 69, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [67, 18, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![224857, 106713, 4828]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3167, 1503, 68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -2, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![45, -2, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![45, 71, 1]] where
  M :=![![![45, -2, 1], ![-118, 2, -1], ![118, -75, 1]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0]], ![![0, -1, -1]], ![![1, -1, -1]]]
  g := ![![![0, -1, 1], ![-1, 1, -1], ![1, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [54, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 72], [0, 1]]
 g := ![![[17, 23], [27], [69], [4, 70], [12], [1]], ![[0, 50], [27], [69], [57, 3], [12], [1]]]
 h' := ![![[31, 72], [38, 60], [6, 63], [3, 19], [5, 17], [19, 31], [0, 1]], ![[0, 1], [0, 13], [61, 10], [8, 54], [21, 56], [31, 42], [31, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [41, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [54, 42, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4390, 616, -16]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 24, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![73, 0, 0], ![1, 1, 0], ![72, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![-118, -43, 2]]]
  hmulB := by decide  
  f := ![![![-45, 2, -1]], ![![1, 0, 0]], ![![-46, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-3, -43, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![45, -2, 1]] ![![1, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3660745, -239970, 72154]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![3660745, -239970, 72154]] 
 ![![79, 0, 0], ![0, 79, 0], ![25, 48, 1]] where
  M :=![![![3660745, -239970, 72154], ![-8514172, 558123, -167816], ![19802288, -1298084, 390307]]]
  hmulB := by decide  
  f := ![![![623, 226, -18]], ![![2124, 1397, 208]], ![![1177, 834, 141]]]
  g := ![![![23505, -46878, 72154], ![-54668, 109029, -167816], ![127147, -253580, 390307]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [29, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 78], [0, 1]]
 g := ![![[75, 44], [49, 20], [32, 46], [53, 1], [26], [1]], ![[44, 35], [78, 59], [75, 33], [11, 78], [26], [1]]]
 h' := ![![[37, 78], [1, 53], [20, 40], [43, 21], [8, 1], [50, 37], [0, 1]], ![[0, 1], [66, 26], [78, 39], [30, 58], [45, 78], [76, 42], [37, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [11, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [29, 42, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![862, -143, 25]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -17, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![623, 226, -18]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![623, 226, -18]] 
 ![![79, 0, 0], ![30, 1, 0], ![48, 0, 1]] where
  M :=![![![623, 226, -18], ![2124, 1397, 208], ![-24544, -6820, 1605]]]
  hmulB := by decide  
  f := ![![![3660745, -239970, 72154]], ![![1282382, -84063, 25276]], ![![2474912, -162236, 48781]]]
  g := ![![![-67, 226, -18], ![-630, 1397, 208], ![1304, -6820, 1605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![3660745, -239970, 72154]] ![![623, 226, -18]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB251I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB251I1 : PrimesBelowBoundCertificateInterval O 31 79 251 where
  m := 11
  g := ![1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB251I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N0, I43N1, I47N1, I53N1, I59N1, I67N1, I73N1, I79N1]
  Il := ![[], [], [I43N0, I43N0, I43N1], [I47N1], [I53N1], [I59N1], [], [I67N1], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
