
import IdealArithmetic.Examples.NF3_1_89240_1.RI3_1_89240_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [5, 34, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36, 34], [14, 0, 3], [0, 1]]
 g := ![![[18, 6, 34], [0, 10], [24, 7, 12], [35, 1], []], ![[30, 1], [8, 16], [24, 6, 30, 26], [], [25, 9]], ![[33, 16, 12, 28], [30, 3], [27, 17, 25, 27], [11, 1], [19, 9]]]
 h' := ![![[21, 36, 34], [7, 0, 16], [28, 26, 26], [10, 26, 7], [0, 0, 1], [0, 1]], ![[14, 0, 3], [31, 30], [21, 32, 33], [30, 1, 33], [20, 25], [21, 36, 34]], ![[0, 1], [32, 7, 21], [21, 16, 15], [8, 10, 34], [27, 12, 36], [14, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 29], []]
 b := ![[], [11, 14, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [5, 34, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-704702, 15355, 36852]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19046, 415, 996]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -17, -5]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-79, -17, -5]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 28, 1]] where
  M :=![![![-79, -17, -5], ![256, -125, -126], ![806, 52, -45]]]
  hmulB := by decide  
  f := ![![![-297, 25, -37]], ![![2196, -185, 274]], ![![1258, -106, 157]]]
  g := ![![![1, 3, -5], ![80, 83, -126], ![46, 32, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [3, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 40], [0, 1]]
 g := ![![[12, 8], [1], [1], [13, 25], [1]], ![[11, 33], [1], [1], [15, 16], [1]]]
 h' := ![![[5, 40], [39, 7], [1, 1], [2, 40], [38, 5], [0, 1]], ![[0, 1], [33, 34], [6, 40], [38, 1], [22, 36], [5, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [13, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [3, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![915, -511, 320]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -231, 320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![297, -25, 37]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![297, -25, 37]] 
 ![![41, 0, 0], ![24, 1, 0], ![32, 0, 1]] where
  M :=![![![297, -25, 37], ![-2196, 185, -274], ![2782, -234, 347]]]
  hmulB := by decide  
  f := ![![![79, 17, 5]], ![![40, 13, 6]], ![![42, 12, 5]]]
  g := ![![![-7, -25, 37], ![52, 185, -274], ![-66, -234, 347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-79, -17, -5]] ![![297, -25, 37]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175425655122350357, 14764547515400403, -21873041830926671]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-175425655122350357, 14764547515400403, -21873041830926671]] 
 ![![43, 0, 0], ![0, 43, 0], ![41, 13, 1]] where
  M :=![![![-175425655122350357, 14764547515400403, -21873041830926671], ![1298165521224547724, -109258970745222477, 161862463785056566], ![-1643773261806583530, 138346745301086294, -204954750153151163]]]
  hmulB := by decide  
  f := ![![![348628271, -27278405, -58749117]], ![![3352891976, 325542173, -100729006]], ![![1333686839, 82608276, -77093158]]]
  g := ![![![16776024649898678, 6956141658545282, -21873041830926671], ![-124144081254948174, -51476069766301345, 161862463785056566], ![157194685917967771, 65180430169582591, -204954750153151163]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 42], [0, 1]]
 g := ![![[11, 21], [41, 4], [17], [29, 11], [1]], ![[0, 22], [0, 39], [17], [13, 32], [1]]]
 h' := ![![[22, 42], [39, 8], [1, 41], [15, 19], [2, 22], [0, 1]], ![[0, 1], [0, 35], [0, 2], [3, 24], [13, 21], [22, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [17, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [41, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2675961, -1447112, 56172]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-115791, -50636, 56172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-348628271, 27278405, 58749117]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-348628271, 27278405, 58749117]] 
 ![![43, 0, 0], ![27, 1, 0], ![28, 0, 1]] where
  M :=![![![-348628271, 27278405, 58749117], ![-3352891976, -325542173, 100729006], ![532820722, -438522224, -403185081]]]
  hmulB := by decide  
  f := ![![![175425655122350357, -14764547515400403, 21873041830926671]], ![![79961096908811905, -6729856096990428, 9969992224417757]], ![![152457944307730082, -12831490133309246, 19009300498118557]]]
  g := ![![![-63491174, 27278405, 58749117], ![60844989, -325542173, 100729006], ![550281466, -438522224, -403185081]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-175425655122350357, 14764547515400403, -21873041830926671]] ![![-348628271, 27278405, 58749117]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70611494949, -5942954989, 8804232093]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![70611494949, -5942954989, 8804232093]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 2, 1]] where
  M :=![![![70611494949, -5942954989, 8804232093], ![-522531371372, 43978397889, -65152104098], ![661643744710, -55686669662, 82497404927]]]
  hmulB := by decide  
  f := ![![![-159059, -43229, -17165]], ![![909112, -271581, -311502]], ![![1047, -29235, -23200]]]
  g := ![![![-2806081770, -501094025, 8804232093], ![20765255806, 3708140555, -65152104098], ![-26293544013, -4695350628, 82497404927]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [9, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 46], [0, 1]]
 g := ![![[13, 21], [27, 27], [1, 25], [44, 12], [1]], ![[0, 26], [17, 20], [37, 22], [3, 35], [1]]]
 h' := ![![[24, 46], [39, 16], [38, 11], [27, 42], [38, 24], [0, 1]], ![[0, 1], [0, 31], [20, 36], [1, 5], [3, 23], [24, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [46, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [9, 23, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33, -1307, -301]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![148, -15, -301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![159059, 43229, 17165]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![159059, 43229, 17165]] 
 ![![47, 0, 0], ![33, 1, 0], ![28, 0, 1]] where
  M :=![![![159059, 43229, 17165], ![-909112, 271581, 311502], ![-1889342, -163384, 72601]]]
  hmulB := by decide  
  f := ![![![-70611494949, 5942954989, -8804232093]], ![![-38460594935, 3237002484, -4795479893]], ![![-56143949006, 4725306582, -7000338373]]]
  g := ![![![-37194, 43229, 17165], ![-395603, 271581, 311502], ![31266, -163384, 72601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![70611494949, -5942954989, 8804232093]] ![![159059, 43229, 17165]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-701371, -148406, -42352]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-701371, -148406, -42352]] 
 ![![53, 0, 0], ![0, 53, 0], ![15, 33, 1]] where
  M :=![![![-701371, -148406, -42352], ![2159604, -1104237, -1102544], ![7082876, 444870, -404559]]]
  hmulB := by decide  
  f := ![![![-17683354071, 1488304098, -2204858480]], ![![130858400036, -11013583297, 16316149744]], ![![73346799003, -6173169473, 9145284945]]]
  g := ![![![-1247, 23570, -42352], ![352788, 665655, -1102544], ![248137, 260289, -404559]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 52], [0, 1]]
 g := ![![[41, 25], [40], [50, 15], [4], [10, 1]], ![[26, 28], [40], [41, 38], [4], [20, 52]]]
 h' := ![![[10, 52], [48, 5], [29, 27], [19, 42], [27, 2], [0, 1]], ![[0, 1], [45, 48], [34, 26], [15, 11], [47, 51], [10, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [33, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [45, 43, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1801, -1238, -484]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![103, 278, -484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17683354071, 1488304098, -2204858480]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-17683354071, 1488304098, -2204858480]] 
 ![![53, 0, 0], ![3, 1, 0], ![51, 0, 1]] where
  M :=![![![-17683354071, 1488304098, -2204858480], ![130858400036, -11013583297, 16316149744], ![-165696542964, 13945705262, -20659962267]]]
  hmulB := by decide  
  f := ![![![-701371, -148406, -42352]], ![![1047, -29235, -23200]], ![![-541265, -134412, -48387]]]
  g := ![![![1703764455, 1488304098, -2204858480], ![-12608009189, -11013583297, 16316149744], ![15964611639, 13945705262, -20659962267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-701371, -148406, -42352]] ![![-17683354071, 1488304098, -2204858480]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [41, 8, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 46, 38], [26, 12, 21], [0, 1]]
 g := ![![[26, 29, 21], [8, 5, 28], [8, 26], [4, 30, 12], [1]], ![[51, 26, 28, 18], [50, 24, 42, 47], [23, 29], [53, 42, 23, 30], [56, 47, 14, 2]], ![[20, 25, 51, 3], [40, 40, 35, 19], [19, 15], [18, 19, 21, 19], [27, 30, 20, 57]]]
 h' := ![![[55, 46, 38], [26, 55, 32], [18, 29, 21], [13, 6, 12], [18, 51, 22], [0, 1]], ![[26, 12, 21], [39, 44, 55], [42, 16, 56], [10, 37, 18], [0, 10, 19], [55, 46, 38]], ![[0, 1], [33, 19, 31], [17, 14, 41], [41, 16, 29], [8, 57, 18], [26, 12, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 5], []]
 b := ![[], [38, 34, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [41, 8, 37, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294693967, -15488857, -24723183]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4994813, -262523, -419037]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [14, 35, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 2, 6], [43, 58, 55], [0, 1]]
 g := ![![[51, 50, 19], [28, 12], [53, 46, 16], [5], [1]], ![[16, 4, 25, 28], [51, 9], [9, 54, 21, 18], [56, 57, 43, 43], [53, 7, 33, 33]], ![[50, 10, 45, 23], [36, 56], [59, 22, 7, 26], [11, 25, 27, 18], [10, 25, 42, 28]]]
 h' := ![![[18, 2, 6], [13, 59, 18], [51, 22, 45], [52, 21, 4], [47, 26], [0, 1]], ![[43, 58, 55], [5, 36, 56], [29, 22, 58], [16, 17, 53], [27, 52, 34], [18, 2, 6]], ![[0, 1], [42, 27, 48], [34, 17, 19], [52, 23, 4], [6, 44, 27], [43, 58, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 45], []]
 b := ![[], [6, 49, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [14, 35, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11956, 0, -1464]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-196, 0, -24]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [9, 38, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 54, 58], [56, 12, 9], [0, 1]]
 g := ![![[58, 51, 60], [33, 21, 55], [28, 59], [9, 37], [3, 1], []], ![[52, 38, 26, 8], [4, 1, 1, 31], [19, 22], [21, 15], [2, 10], [8, 14]], ![[35, 25, 61, 22], [0, 55, 66, 22], [46, 24], [25, 49], [30, 35], [57, 14]]]
 h' := ![![[14, 54, 58], [38, 54, 23], [31, 38, 51], [45, 4, 40], [40, 11, 38], [0, 0, 1], [0, 1]], ![[56, 12, 9], [28, 64, 58], [53, 16, 2], [36, 13, 42], [15, 36, 22], [57, 10, 12], [14, 54, 58]], ![[0, 1], [9, 16, 53], [56, 13, 14], [66, 50, 52], [31, 20, 7], [10, 57, 54], [56, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 66], []]
 b := ![[], [0, 3, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [9, 38, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3000260, -250312, -143916]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44780, -3736, -2148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18625995607257, 1567640702115, -2322392245171]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-18625995607257, 1567640702115, -2322392245171]] 
 ![![71, 0, 0], ![0, 71, 0], ![43, 47, 1]] where
  M :=![![![-18625995607257, 1567640702115, -2322392245171], ![137834031624148, -11600681255741, 17185910107262], ![-174529281548826, 14689105014082, -21761277011487]]]
  hmulB := by decide  
  f := ![![![-2834273, -685873, -239189]], ![![12501216, -4652703, -5008606]], ![![6997933, -3462104, -3481016]]]
  g := ![![![1144181280776, 1559437693312, -2322392245171], ![-8467043704058, -11539978257705, 17185910107262], ![10721206055565, 14612241190901, -21761277011487]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [44, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 70], [0, 1]]
 g := ![![[47, 9], [49, 3], [64, 5], [64], [10], [1]], ![[37, 62], [22, 68], [19, 66], [64], [10], [1]]]
 h' := ![![[62, 70], [45, 3], [24, 43], [49, 54], [5, 63], [27, 62], [0, 1]], ![[0, 1], [18, 68], [63, 28], [60, 17], [6, 8], [37, 9], [62, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [27, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [44, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16296, -8785, 85]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-281, -180, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2834273, -685873, -239189]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-2834273, -685873, -239189]] 
 ![![71, 0, 0], ![52, 1, 0], ![51, 0, 1]] where
  M :=![![![-2834273, -685873, -239189], ![12501216, -4652703, -5008606], ![31169830, 2360196, -1462527]]]
  hmulB := by decide  
  f := ![![![-18625995607257, 1567640702115, -2322392245171]], ![![-11700249858496, 984741341609, -1458851924530]], ![![-15837395176323, 1332940574957, -1974694105848]]]
  g := ![![![634222, -685873, -239189], ![7181418, -4652703, -5008606], ![-239035, 2360196, -1462527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-18625995607257, 1567640702115, -2322392245171]] ![![-2834273, -685873, -239189]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39481, -1957, -5759]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![39481, -1957, -5759]] 
 ![![73, 0, 0], ![0, 73, 0], ![35, 20, 1]] where
  M :=![![![39481, -1957, -5759], ![330108, 39369, -4138], ![-93818, 42270, 43395]]]
  hmulB := by decide  
  f := ![![![25799055, -2171355, 3216769]], ![![-190915312, 16068221, -23804378]], ![![-36624617, 3082479, -4566560]]]
  g := ![![![3302, 1551, -5759], ![6506, 1673, -4138], ![-22091, -11310, 43395]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [72, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 72], [0, 1]]
 g := ![![[44, 72], [69], [27], [9, 64], [38], [1]], ![[0, 1], [69], [27], [51, 9], [38], [1]]]
 h' := ![![[44, 72], [53, 27], [35, 54], [9, 10], [39, 8], [1, 44], [0, 1]], ![[0, 1], [0, 46], [2, 19], [11, 63], [26, 65], [39, 29], [44, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [8, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [72, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5534, -868, -58]
  a := ![-2, -8, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, 4, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25799055, -2171355, 3216769]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![25799055, -2171355, 3216769]] 
 ![![73, 0, 0], ![61, 1, 0], ![5, 0, 1]] where
  M :=![![![25799055, -2171355, 3216769], ![-190915312, 16068221, -23804378], ![241742274, -20346028, 30141765]]]
  hmulB := by decide  
  f := ![![![39481, -1957, -5759]], ![![37513, -1096, -4869]], ![![1419, 445, 200]]]
  g := ![![![1947505, -2171355, 3216769], ![-14411711, 16068221, -23804378], ![18248509, -20346028, 30141765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![39481, -1957, -5759]] ![![25799055, -2171355, 3216769]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3007, 253, -375]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-3007, 253, -375]] 
 ![![79, 0, 0], ![0, 79, 0], ![59, 64, 1]] where
  M :=![![![-3007, 253, -375], ![22256, -1873, 2774], ![-28174, 2372, -3513]]]
  hmulB := by decide  
  f := ![![![1, 9, 7]], ![![-388, 21, 58]], ![![-317, 23, 52]]]
  g := ![![![242, 307, -375], ![-1790, -2271, 2774], ![2267, 2876, -3513]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [77, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 78], [0, 1]]
 g := ![![[29, 42], [62, 32], [4, 16], [38, 55], [46], [1]], ![[16, 37], [22, 47], [63, 63], [68, 24], [46], [1]]]
 h' := ![![[58, 78], [45, 11], [8, 36], [76, 75], [17, 56], [2, 58], [0, 1]], ![[0, 1], [51, 68], [42, 43], [2, 4], [26, 23], [48, 21], [58, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [4, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [77, 21, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-111327, -62975, 4725]
  a := ![27, 40, 95]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4938, -4625, 4725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -9, -7]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1, -9, -7]] 
 ![![79, 0, 0], ![43, 1, 0], ![69, 0, 1]] where
  M :=![![![-1, -9, -7], ![388, -21, -58], ![270, 58, 17]]]
  hmulB := by decide  
  f := ![![![3007, -253, 375]], ![![1355, -114, 169]], ![![2983, -251, 372]]]
  g := ![![![11, -9, -7], ![67, -21, -58], ![-43, 58, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-3007, 253, -375]] ![![-1, -9, -7]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB85I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB85I1 : PrimesBelowBoundCertificateInterval O 31 79 85 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB85I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I47N1, I53N1, I71N1, I73N1, I79N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [], [], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
