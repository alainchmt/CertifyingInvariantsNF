
import IdealArithmetic.Examples.NF3_1_334235_1.RI3_1_334235_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 4, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-35, 4, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![2, 4, 1]] where
  M :=![![![-35, 4, 1], ![-212, 20, 5], ![-1060, 63, 25]]]
  hmulB := by decide  
  f := ![![![5, -1, 0]], ![![0, 5, -1]], ![![6, -1, 0]]]
  g := ![![![-1, 0, 1], ![-6, 0, 5], ![-30, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 36], [0, 1]]
 g := ![![[33, 16], [25], [12, 10], [27], [1]], ![[16, 21], [25], [6, 27], [27], [1]]]
 h' := ![![[29, 36], [34, 4], [24, 32], [21, 11], [2, 29], [0, 1]], ![[0, 1], [2, 33], [27, 5], [7, 26], [29, 8], [29, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-601, -55, 51]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -7, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![12, 0, 1]] where
  M :=![![![-5, 1, 0], ![0, -5, 1], ![-212, 55, -4]]]
  hmulB := by decide  
  f := ![![![35, -4, -1]], ![![36, -4, -1]], ![![40, -3, -1]]]
  g := ![![![-1, 1, 0], ![4, -5, 1], ![-52, 55, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-35, 4, 1]] ![![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12919044989, -20676886060, -2624144965]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![12919044989, -20676886060, -2624144965]] 
 ![![41, 0, 0], ![0, 41, 0], ![1, 33, 1]] where
  M :=![![![12919044989, -20676886060, -2624144965], ![556318732580, -131408928086, -23301031025], ![4939818577300, -725237973795, -154709959111]]]
  hmulB := by decide  
  f := ![![![-83694569831706524431, 31604649256694017085, -3340406990037220110]], ![![708166281887890663320, -267416954283753630481, 28264242266656796975]], ![![421799350535059619669, -159279395989101494923, 16834801848598542599]]]
  g := ![![![379102194, 1607802385, -2624144965], ![14137067405, 15549392579, -23301031025], ![124256793571, 106833918948, -154709959111]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 40], [0, 1]]
 g := ![![[37, 1], [20], [16], [15, 16], [1]], ![[0, 40], [20], [16], [38, 25], [1]]]
 h' := ![![[4, 40], [37, 1], [4, 26], [26, 4], [40, 4], [0, 1]], ![[0, 1], [0, 40], [26, 15], [1, 37], [15, 37], [4, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [14, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![601, -2143, 601]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -536, 601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90201580372927, -37452884812080, -5686272123089]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![90201580372927, -37452884812080, -5686272123089]] 
 ![![41, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![90201580372927, -37452884812080, -5686272123089], ![1205489690094868, -222543386396968, -43139156935169], ![9145501270255828, -1167163941339427, -265682543332137]]]
  hmulB := by decide  
  f := ![![![-8775424465181032295291152453, 3313765909285911700597084957, -350243621336223729795647368]], ![![312772596756395235357053045, -118108835943218427557857634, 12483339965759069810534293]], ![![-22386725180397754037914946337, 8453649965047496469035612512, -893496118410220306012358128]]]
  g := ![![![13171189124864, -37452884812080, -5686272123089], ![102119160334981, -222543386396968, -43139156935169], ![636174946087618, -1167163941339427, -265682543332137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![12919044989, -20676886060, -2624144965]] ![![90201580372927, -37452884812080, -5686272123089]]
  ![![41, 0, 0]] where
 M := ![![![-47759575804422488224233297, 7180456120076977652834015, 1515711735668486514433324]]]
 hmul := by decide  
 g := ![![![![-1164867702546889956688617, 175133076099438479337415, 36968578918743573522764]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48555, -5752, -1358]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![48555, -5752, -1358]] 
 ![![43, 0, 0], ![25, 1, 0], ![20, 0, 1]] where
  M :=![![![48555, -5752, -1358], ![287896, -26135, -7110], ![1507320, -103154, -33245]]]
  hmulB := by decide  
  f := ![![![-135433135, 51142108, -5405390]], ![![-52090365, 19670305, -2079024]], ![![-288484812, 108937310, -11513969]]]
  g := ![![![5105, -5752, -1358], ![25197, -26135, -7110], ![110490, -103154, -33245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, -16, -4]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![151, -16, -4]] 
 ![![43, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![151, -16, -4], ![848, -69, -20], ![4240, -252, -89]]]
  hmulB := by decide  
  f := ![![![1101, -416, 44]], ![![500, -189, 20]], ![![2679, -1012, 107]]]
  g := ![![![17, -16, -4], ![80, -69, -20], ![331, -252, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24475724233, -9242495436, 976871982]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![24475724233, -9242495436, 976871982]] 
 ![![43, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![24475724233, -9242495436, 976871982], ![-207096860184, 78203683243, -8265623454], ![1752312172248, -661706150154, 69938059789]]]
  hmulB := by decide  
  f := ![![![3303811, 37776, -41682]], ![![2664152, 51631, -31110]], ![![633920, 207534, 15673]]]
  g := ![![![7265595403, -9242495436, 976871982], ![-61476505496, 78203683243, -8265623454], ![520172197648, -661706150154, 69938059789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![48555, -5752, -1358]] ![![151, -16, -4]]
  ![![-3303811, -37776, 41682]] where
 M := ![![![-3303811, -37776, 41682]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-3303811, -37776, 41682]] ![![24475724233, -9242495436, 976871982]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-285, 34, 8]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-285, 34, 8]] 
 ![![47, 0, 0], ![0, 47, 0], ![29, 16, 1]] where
  M :=![![![-285, 34, 8], ![-1696, 155, 42], ![-8904, 614, 197]]]
  hmulB := by decide  
  f := ![![![101, -38, 4]], ![![-848, 321, -34]], ![![-73, 28, -3]]]
  g := ![![![-11, -2, 8], ![-62, -11, 42], ![-311, -54, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 46], [0, 1]]
 g := ![![[27, 17], [13, 6], [40, 27], [28, 28], [1]], ![[41, 30], [29, 41], [18, 20], [40, 19], [1]]]
 h' := ![![[34, 46], [39, 8], [26, 37], [37, 11], [3, 34], [0, 1]], ![[0, 1], [29, 39], [15, 10], [35, 36], [31, 13], [34, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [22, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [44, 13, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3520, -382, 170]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -66, 170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -38, 4]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![101, -38, 4]] 
 ![![47, 0, 0], ![30, 1, 0], ![40, 0, 1]] where
  M :=![![![101, -38, 4], ![-848, 321, -34], ![7208, -2718, 287]]]
  hmulB := by decide  
  f := ![![![-285, 34, 8]], ![![-218, 25, 6]], ![![-432, 42, 11]]]
  g := ![![![23, -38, 4], ![-194, 321, -34], ![1644, -2718, 287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-285, 34, 8]] ![![101, -38, 4]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-206117, -719, 2794]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-206117, -719, 2794]] 
 ![![53, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-206117, -719, 2794], ![-592328, -52447, 2075], ![-439900, -478203, -50372]]]
  hmulB := by decide  
  f := ![![![-3634131509, 1372316650, -145044993]], ![![580179972, -219086908, 23156069]], ![![-4909086628, 1853763767, -195930839]]]
  g := ![![![-3889, -719, 2794], ![-11176, -52447, 2075], ![-8300, -478203, -50372]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22221339768199, 8391197311844, -886895276945]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-22221339768199, 8391197311844, -886895276945]] 
 ![![53, 0, 0], ![1, 1, 0], ![52, 0, 1]] where
  M :=![![![-22221339768199, 8391197311844, -886895276945], ![188021798712340, -71000580000174, 7504302034899], ![-1590912031398588, 600758410631785, -63496277965275]]]
  hmulB := by decide  
  f := ![![![-157293135, 16479725, 4144674]], ![![-19546491, 1644220, 467341]], ![![-236822936, 20992769, 5788894]]]
  g := ![![![292566364549, 8391197311844, -886895276945], ![-2475496737778, -71000580000174, 7504302034899], ![20945962493659, 600758410631785, -63496277965275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1083, 92, 26]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-1083, 92, 26]] 
 ![![53, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![-1083, 92, 26], ![-5512, 347, 118], ![-25016, 978, 465]]]
  hmulB := by decide  
  f := ![![![-45951, 17352, -1834]], ![![-36881, 13927, -1472]], ![![-104555, 39482, -4173]]]
  g := ![![![-133, 92, 26], ![-547, 347, 118], ![-1843, 978, 465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-206117, -719, 2794]] ![![-22221339768199, 8391197311844, -886895276945]]
  ![![45951, -17352, 1834]] where
 M := ![![![45951, -17352, 1834]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![45951, -17352, 1834]] ![![-1083, 92, 26]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1801, 399, 22]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![1801, 399, 22]] 
 ![![59, 0, 0], ![29, 1, 0], ![44, 0, 1]] where
  M :=![![![1801, 399, 22], ![-4664, 3011, 421], ![-89252, 18491, 3432]]]
  hmulB := by decide  
  f := ![![![-2549041, 962566, -101737]], ![![-887355, 335082, -35416]], ![![-4994128, 1885877, -199325]]]
  g := ![![![-182, 399, 22], ![-1873, 3011, 421], ![-13161, 18491, 3432]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, -227, 24]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![601, -227, 24]] 
 ![![59, 0, 0], ![44, 1, 0], ![11, 0, 1]] where
  M :=![![![601, -227, 24], ![-5088, 1921, -203], ![43036, -16253, 1718]]]
  hmulB := by decide  
  f := ![![![919, -86, -23]], ![![768, -70, -19]], ![![563, -35, -12]]]
  g := ![![![175, -227, 24], ![-1481, 1921, -203], ![12530, -16253, 1718]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![1801, 399, 22]] ![![601, -227, 24]]
  ![![-919, 86, 23]] where
 M := ![![![-919, 86, 23]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-919, 86, 23]] ![![601, -227, 24]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3949209, 197468, 78499]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-3949209, 197468, 78499]] 
 ![![61, 0, 0], ![28, 1, 0], ![9, 0, 1]] where
  M :=![![![-3949209, 197468, 78499], ![-16641788, 368236, 275967], ![-58505004, -1463603, 644203]]]
  hmulB := by decide  
  f := ![![![-641124865009, 242100849901, -25588493792]], ![![-205356320268, 77546422519, -8196155247]], ![![-847061365249, 319866359328, -33807805108]]]
  g := ![![![-166964, 197468, 78499], ![-482559, 368236, 275967], ![-382327, -1463603, 644203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163140611821574071, -61604974211720466, 6511247279047317]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![163140611821574071, -61604974211720466, 6511247279047317]] 
 ![![61, 0, 0], ![45, 1, 0], ![49, 0, 1]] where
  M :=![![![163140611821574071, -61604974211720466, 6511247279047317], ![-1380384423158031204, 521259212169176506, -55093726932673149], ![11679870109726707588, -4410539404455054399, 466165485236503357]]]
  hmulB := by decide  
  f := ![![![16312898191, -1175393121, -366766968]], ![![13308770751, -930360254, -295847109]], ![![18463441807, -1059974928, -383164370]]]
  g := ![![![42890382535666828, -61604974211720466, 6511247279047317], ![-362909120509344093, 521259212169176506, -55093726932673149], ![3070689090715008050, -4410539404455054399, 466165485236503357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5419, -28, -79]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![5419, -28, -79]] 
 ![![61, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![5419, -28, -79], ![16748, 1074, -107], ![22684, 10863, 967]]]
  hmulB := by decide  
  f := ![![![2200899, -831101, 87842]], ![![1426568, -538699, 56937]], ![![3088254, -1166183, 123258]]]
  g := ![![![129, -28, -79], ![-546, 1074, -107], ![-8398, 10863, 967]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-3949209, 197468, 78499]] ![![163140611821574071, -61604974211720466, 6511247279047317]]
  ![![-2200899, 831101, -87842]] where
 M := ![![![-2200899, 831101, -87842]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-2200899, 831101, -87842]] ![![5419, -28, -79]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-132930988047, 17667270305, 3944741424]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-132930988047, 17667270305, 3944741424]] 
 ![![67, 0, 0], ![0, 67, 0], ![57, 47, 1]] where
  M :=![![![-132930988047, 17667270305, 3944741424], ![-836285181888, 84029790273, 21612011729], ![-4581746486548, 352375463207, 105641802002]]]
  hmulB := by decide  
  f := ![![![-18828594364900889129, 7110032611384826326, -751484455390119979]], ![![159314704542705435548, -60160239411357487974, 6358548155994706347]], ![![75620134710998911117, -28555590154663470889, 3018141165957486237]]]
  g := ![![![-5340018645, -2503516069, 3944741424], ![-30868206723, -13906488970, 21612011729], ![-158258644786, -68847600461, 105641802002]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [50, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 66], [0, 1]]
 g := ![![[6, 23], [63, 17], [56], [39], [19], [1]], ![[7, 44], [55, 50], [56], [39], [19], [1]]]
 h' := ![![[35, 66], [66, 31], [63, 33], [7, 49], [9, 46], [17, 35], [0, 1]], ![[0, 1], [12, 36], [12, 34], [47, 18], [11, 21], [36, 32], [35, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [52, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [50, 32, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-553, -1709, 397]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346, -304, 397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18828594364900889129, 7110032611384826326, -751484455390119979]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-18828594364900889129, 7110032611384826326, -751484455390119979]] 
 ![![67, 0, 0], ![19, 1, 0], ![41, 0, 1]] where
  M :=![![![-18828594364900889129, 7110032611384826326, -751484455390119979], ![159314704542705435548, -60160239411357487974, 6358548155994706347], ![-1348012209070877745564, 509034853122414284633, -53801691255362781627]]]
  hmulB := by decide  
  f := ![![![-132930988047, 17667270305, 3944741424]], ![![-50178715743, 6264297404, 1441225355]], ![![-149730104425, 16070649936, 3990689558]]]
  g := ![![![-1837438079256980152, 7110032611384826326, -751484455390119979], ![15547145954667384281, -60160239411357487974, 6358548155994706347], ![-131549329506371270252, 509034853122414284633, -53801691255362781627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-132930988047, 17667270305, 3944741424]] ![![-18828594364900889129, 7110032611384826326, -751484455390119979]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8237575732529187385, 3110664076242266662, -328777071358781190]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-8237575732529187385, 3110664076242266662, -328777071358781190]] 
 ![![71, 0, 0], ![0, 71, 0], ![6, 11, 1]] where
  M :=![![![-8237575732529187385, 3110664076242266662, -328777071358781190], ![69700739128061612280, -26320314657262152835, 2781887004883485472], ![-589760045035298920064, 222704524396653313240, -23538427652378667363]]]
  hmulB := by decide  
  f := ![![![-14162354575, 1290811314, 350369566]], ![![-74278347992, 5107971555, 1641180880]], ![![-17605159182, 1125621907, 378934641]]]
  g := ![![![-88238215554598595, 94749462833645912, -328777071358781190], ![746611508433249288, -801705235365922437, 2781887004883485472], ![-6317316607338407266, 6783482092574910623, -23538427652378667363]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [47, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 70], [0, 1]]
 g := ![![[61, 10], [67, 58], [], [20], [19], [1]], ![[4, 61], [63, 13], [], [20], [19], [1]]]
 h' := ![![[44, 70], [46, 9], [0, 49], [7], [38, 37], [24, 44], [0, 1]], ![[0, 1], [16, 62], [26, 22], [7], [33, 34], [43, 27], [44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [1, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [47, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-589, -74, 32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -6, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14162354575, 1290811314, 350369566]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-14162354575, 1290811314, 350369566]] 
 ![![71, 0, 0], ![59, 1, 0], ![69, 0, 1]] where
  M :=![![![-14162354575, 1290811314, 350369566], ![-74278347992, 5107971555, 1641180880], ![-347930346560, 15986600408, 6749152435]]]
  hmulB := by decide  
  f := ![![![-8237575732529187385, 3110664076242266662, -328777071358781190]], ![![-5863608860438879485, 2214209378042698313, -234027608525135278]], ![![-16312010853236800699, 6159723178272812858, -651042895438515063]]]
  g := ![![![-1612615805, 1290811314, 350369566], ![-6885776767, 5107971555, 1641180880], ![-24744102657, 15986600408, 6749152435]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-8237575732529187385, 3110664076242266662, -328777071358781190]] ![![-14162354575, 1290811314, 350369566]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-130620883900709, 4694761694375, 2379319852748]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-130620883900709, 4694761694375, 2379319852748]] 
 ![![73, 0, 0], ![31, 1, 0], ![61, 0, 1]] where
  M :=![![![-130620883900709, 4694761694375, 2379319852748], ![-504415808782576, 241708000431, 7074081547123], ![-1499705287990076, -115341323690811, 7315789547554]]]
  hmulB := by decide  
  f := ![![![817702214405020298905582527, -308779789831745364077507378, 32636026426324596445998737]], ![![252464808824312531774264741, -95335476944263468259824872, 10076343230282763317732222]], ![![1485237163296649876316717343, -560853585882403066780995309, 59278596115797982452190786]]]
  g := ![![![-5771191882794, 4694761694375, 2379319852748], ![-12923667550280, 241708000431, 7074081547123], ![22323460055127, -115341323690811, 7315789547554]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2229534712087, -841914388506, 88984904896]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![2229534712087, -841914388506, 88984904896]] 
 ![![73, 0, 0], ![50, 1, 0], ![55, 0, 1]] where
  M :=![![![2229534712087, -841914388506, 88984904896], ![-18864799837952, 7123704481367, -752929483610], ![159621050525320, -60275921436502, 6370774997757]]]
  hmulB := by decide  
  f := ![![![8561599, 3667250, 313828]], ![![4952718, 2865543, 269486]], ![![-5110967, 4851048, 644709]]]
  g := ![![![540151840659, -841914388506, 88984904896], ![-4570395922024, 7123704481367, -752929483610], ![38671568458545, -60275921436502, 6370774997757]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52003400942113, 19637465730878, -2075553101737]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-52003400942113, 19637465730878, -2075553101737]] 
 ![![73, 0, 0], ![64, 1, 0], ![65, 0, 1]] where
  M :=![![![-52003400942113, 19637465730878, -2075553101737], ![440017257568244, -166158821537648, 17561912629141], ![-3723125477377892, 1405922452170999, -148596908908507]]]
  hmulB := by decide  
  f := ![![![314510323, -18853883, -6621222]], ![![294963832, -17209663, -6153881]], ![![354025935, -16752522, -6924814]]]
  g := ![![![-16080688439800, 19637465730878, -2075553101737], ![136063801576487, -166158821537648, 17561912629141], ![-1151278949825601, 1405922452170999, -148596908908507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-130620883900709, 4694761694375, 2379319852748]] ![![2229534712087, -841914388506, 88984904896]]
  ![![-314510323, 18853883, 6621222]] where
 M := ![![![-314510323, 18853883, 6621222]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-314510323, 18853883, 6621222]] ![![-52003400942113, 19637465730878, -2075553101737]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-266872521, 100776101, -10651382]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-266872521, 100776101, -10651382]] 
 ![![79, 0, 0], ![0, 79, 0], ![68, 47, 1]] where
  M :=![![![-266872521, 100776101, -10651382], ![2258092984, -852698531, 90124719], ![-19106440428, 7214952529, -762573812]]]
  hmulB := by decide  
  f := ![![![37901, 2254, -263]], ![![55756, 23436, 1991]], ![![60452, 17975, 1280]]]
  g := ![![![5790145, 7612545, -10651382], ![-48992252, -64412156, 90124719], ![414538972, 545011667, -762573812]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [44, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 78], [0, 1]]
 g := ![![[27, 9], [77, 52], [64, 5], [], [9], [1]], ![[0, 70], [0, 27], [49, 74], [], [9], [1]]]
 h' := ![![[76, 78], [9, 3], [28, 62], [0, 20], [39], [35, 76], [0, 1]], ![[0, 1], [0, 76], [0, 17], [19, 59], [39], [44, 3], [76, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [53, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [44, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8220, 2028, 460]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-500, -248, 460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37901, 2254, -263]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![37901, 2254, -263]] 
 ![![79, 0, 0], ![31, 1, 0], ![66, 0, 1]] where
  M :=![![![37901, 2254, -263], ![55756, 23436, 1991], ![-422092, 165261, 25427]]]
  hmulB := by decide  
  f := ![![![-266872521, 100776101, -10651382]], ![![-76138673, 28751400, -3038837]], ![![-464810466, 175521205, -18551456]]]
  g := ![![![-185, 2254, -263], ![-10154, 23436, 1991], ![-91435, 165261, 25427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-266872521, 100776101, -10651382]] ![![37901, 2254, -263]]
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


lemma PB164I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB164I1 : PrimesBelowBoundCertificateInterval O 31 79 164 where
  m := 11
  g := ![2, 2, 3, 2, 3, 3, 3, 2, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB164I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N0, I43N1, I43N2, I47N1, I53N0, I53N1, I53N2, I59N0, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
