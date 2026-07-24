
import IdealArithmetic.Examples.NF3_1_171444_1.RI3_1_171444_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135982136301264667523, -13201965971771881571, -12308606875297166287]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-135982136301264667523, -13201965971771881571, -12308606875297166287]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 15, 1]] where
  M :=![![![-135982136301264667523, -13201965971771881571, -12308606875297166287], ![-1011092481967317066102, -98162956578898453378, -91520402705928455713], ![-1376181056499476849142, -133607957435319398589, -124566888522442216520]]]
  hmulB := by decide  
  f := ![![![1148102281, 1389556321, -1134364801]], ![![-87970071438, 2027275562, 7202973125]], ![![-33052830299, 836419204, 2651466018]]]
  g := ![![![649452785881040384, 4633165869126638182, -12308606875297166287], ![4828993329993320491, 34449813081352118441, -91520402705928455713], ![6572662007899242314, 46889064064900374303, -124566888522442216520]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[27, 30], [25], [35, 9], [33], [1]], ![[0, 7], [25], [1, 28], [33], [1]]]
 h' := ![![[25, 36], [18, 20], [5, 32], [7, 34], [16, 25], [0, 1]], ![[0, 1], [0, 17], [28, 5], [6, 3], [12, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [22, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![662, 1094, -228]
  a := ![-3, 1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98, 122, -228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1148102281, 1389556321, -1134364801]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1148102281, 1389556321, -1134364801]] 
 ![![37, 0, 0], ![20, 1, 0], ![11, 0, 1]] where
  M :=![![![1148102281, 1389556321, -1134364801], ![-87970071438, 2027275562, 7202973125], ![81671020854, -17525855055, 4806388204]]]
  hmulB := by decide  
  f := ![![![-135982136301264667523, -13201965971771881571, -12308606875297166287]], ![![-100830681297097578826, -9789250703090164454, -9126825411131669769]], ![![-77621204211172653835, -7535934679048921510, -7025988220289487721]]]
  g := ![![![-382838144, 1389556321, -1134364801], ![-5614818569, 2027275562, 7202973125], ![10251833830, -17525855055, 4806388204]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-135982136301264667523, -13201965971771881571, -12308606875297166287]] ![![1148102281, 1389556321, -1134364801]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [12, 4, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 15, 33], [30, 25, 8], [0, 1]]
 g := ![![[29, 10, 1], [12, 31], [11, 36], [14, 10, 1], []], ![[12, 16, 10, 2], [35, 4], [], [40, 23, 10, 2], [31, 23]], ![[4, 40, 36, 37], [21, 33], [20, 36], [2, 3, 36, 37], [15, 23]]]
 h' := ![![[21, 15, 33], [28, 0, 1], [7, 30, 21], [37, 29, 6], [0, 0, 1], [0, 1]], ![[30, 25, 8], [15, 25, 25], [36, 32, 39], [35, 11], [28, 25, 25], [21, 15, 33]], ![[0, 1], [10, 16, 15], [37, 20, 22], [20, 1, 35], [23, 16, 15], [30, 25, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 17], []]
 b := ![[], [8, 26, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [12, 4, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1029264, 10332, -34440]
  a := ![3, -3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25104, 252, -840]
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

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [40, 22, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 8, 38], [21, 34, 5], [0, 1]]
 g := ![![[31, 25, 23], [22, 40, 35], [13, 9], [31, 28, 1], []], ![[12, 3, 21, 6], [6, 37, 19, 15], [20, 6], [37, 4, 39, 25], [18, 25]], ![[14, 31, 14, 12], [40, 16, 41, 42], [33, 16], [6, 31, 35, 19], [8, 25]]]
 h' := ![![[7, 8, 38], [23, 27, 18], [2, 12, 11], [7, 4, 40], [0, 0, 1], [0, 1]], ![[21, 34, 5], [2, 23, 4], [15, 33, 13], [27, 14, 7], [17, 6, 34], [7, 8, 38]], ![[0, 1], [16, 36, 21], [37, 41, 19], [29, 25, 39], [35, 37, 8], [21, 34, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 16], []]
 b := ![[], [33, 38, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [40, 22, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2304795700, 77504361, -87934699]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53599900, 1802427, -2044993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [9, 41, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 34, 25], [17, 12, 22], [0, 1]]
 g := ![![[34, 30, 7], [22, 44, 16], [27, 20, 28], [8, 40, 1], []], ![[12, 32, 43, 42], [9, 1, 1, 14], [10, 46, 15, 42], [18, 45, 39, 28], [4, 14]], ![[36, 6, 34, 23], [13, 37, 15, 22], [44, 44, 9, 20], [1, 19, 12, 5], [7, 14]]]
 h' := ![![[23, 34, 25], [37, 35, 30], [39, 43, 4], [22, 17, 34], [0, 0, 1], [0, 1]], ![[17, 12, 22], [28, 24, 13], [39, 25, 42], [20, 43, 34], [23, 5, 12], [23, 34, 25]], ![[0, 1], [33, 35, 4], [29, 26, 1], [5, 34, 26], [38, 42, 34], [17, 12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 5], []]
 b := ![[], [14, 32, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [9, 41, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2379187, 100157, 26367]
  a := ![-4, 3, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50621, 2131, 561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-238092019753100813661419643682551824327, -23115409335583752690848825554841280255, -21551220998571341534347659524151685055]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-238092019753100813661419643682551824327, -23115409335583752690848825554841280255, -21551220998571341534347659524151685055]] 
 ![![53, 0, 0], ![11, 1, 0], ![35, 0, 1]] where
  M :=![![![-238092019753100813661419643682551824327, -23115409335583752690848825554841280255, -21551220998571341534347659524151685055], ![-1770328498556874828129510413041817364910, -171874168420374377901875499079407173962, -160243677012073857679440612853199366585], ![-2409564492809555095160945192015246231830, -233935054310259934564821922704289345205, -218104987091541883283573150189089734472]]]
  hmulB := by decide  
  f := ![![![56061783823914756861, 8291147039152039085, -11631113138646741265]], ![![-5608059150007035803, 3061046801749596797, -1694839159034880390]], ![![43831042554044610265, 2309497763954899120, -6027807598344823883]]]
  g := ![![![14537173922421083389435575863509645951, -23115409335583752690848825554841280255, -21551220998571341534347659524151685055], ![108090868858298648067387575975351686399, -171874168420374377901875499079407173962, -160243677012073857679440612853199366585], ![147120672694476794339191626685850514565, -233935054310259934564821922704289345205, -218104987091541883283573150189089734472]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-304612705, 82071506, -30199512]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-304612705, 82071506, -30199512]] 
 ![![53, 0, 0], ![45, 1, 0], ![6, 0, 1]] where
  M :=![![![-304612705, 82071506, -30199512], ![-2251817948, -326285187, 462229524], ![5780533168, -556736668, -162142175]]]
  hmulB := by decide  
  f := ![![![-310244714933447757, -30120428174471566, -28082219732114400]], ![![-306940200130627249, -29799605946150337, -27783107108001732]], ![![-94363023709309174, -9161331494629688, -8541396642195791]]]
  g := ![![![-72011951, 82071506, -30199512], ![182219591, -326285187, 462229524], ![600123326, -556736668, -162142175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71507457551, 18262926897, -6352195595]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-71507457551, 18262926897, -6352195595]] 
 ![![53, 0, 0], ![50, 1, 0], ![16, 0, 1]] where
  M :=![![![-71507457551, 18262926897, -6352195595], ![-471649793806, -77065993258, 103225365787], ![1295877066290, -119104396529, -40540139464]]]
  hmulB := by decide  
  f := ![![![-15418861013156921887035, -1496956026401863852963, -1395659046386298574429]], ![![-16709239366444409585132, -1622233739888219877988, -1512459387247403970069]], ![![-7598969689220823044618, -737753810804678781303, -687831012999376712868]]]
  g := ![![![-16660729677, 18262926897, -6352195595], ![32642339934, -77065993258, 103225365787], ![149051681588, -119104396529, -40540139464]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-238092019753100813661419643682551824327, -23115409335583752690848825554841280255, -21551220998571341534347659524151685055]] ![![-304612705, 82071506, -30199512]]
  ![![15418861013156921887035, 1496956026401863852963, 1395659046386298574429]] where
 M := ![![![15418861013156921887035, 1496956026401863852963, 1395659046386298574429]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![15418861013156921887035, 1496956026401863852963, 1395659046386298574429]] ![![-71507457551, 18262926897, -6352195595]]
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
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6541, 2562, -1236]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-6541, 2562, -1236]] 
 ![![59, 0, 0], ![0, 59, 0], ![42, 28, 1]] where
  M :=![![![-6541, 2562, -1236], ![-93756, -6631, 14136], ![172824, -21192, -1507]]]
  hmulB := by decide  
  f := ![![![-5246831, -509394, -474924]], ![![-39012708, -3787589, -3531288]], ![![-23149530, -2247496, -2095411]]]
  g := ![![![769, 630, -1236], ![-11652, -6821, 14136], ![4002, 356, -1507]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [27, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 58], [0, 1]]
 g := ![![[24, 35], [10, 49], [48], [15, 27], [1, 1]], ![[0, 24], [0, 10], [48], [42, 32], [2, 58]]]
 h' := ![![[1, 58], [25, 34], [7, 52], [8, 15], [32, 33], [0, 1]], ![[0, 1], [0, 25], [0, 7], [23, 44], [6, 26], [1, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [43, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [27, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![530, 1140, -642]
  a := ![-3, 1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![466, 324, -642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5246831, 509394, 474924]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![5246831, 509394, 474924]] 
 ![![59, 0, 0], ![8, 1, 0], ![50, 0, 1]] where
  M :=![![![5246831, 509394, 474924], ![39012708, 3787589, 3531288], ![53099544, 5155224, 4806377]]]
  hmulB := by decide  
  f := ![![![6541, -2562, 1236]], ![![2476, -235, -72]], ![![2614, -1812, 1073]]]
  g := ![![![-382619, 509394, 474924], ![-2844956, 3787589, 3531288], ![-3872222, 5155224, 4806377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-6541, 2562, -1236]] ![![5246831, 509394, 474924]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20546951333, 13512928522, -7897799530]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-20546951333, 13512928522, -7897799530]] 
 ![![61, 0, 0], ![1, 1, 0], ![41, 0, 1]] where
  M :=![![![-20546951333, 13512928522, -7897799530], ![-604798105356, -18264280795, 73179771602], ![875691493980, -129697250934, 8761576249]]]
  hmulB := by decide  
  f := ![![![-9331191311938862338313, -905928333876047387042, -844625394635572405894]], ![![-1290378353287487698097, -125277713486356025025, -116800340861105395640]], ![![-7819891323936098842417, -759202215597185071660, -707828033386921861561]]]
  g := ![![![4749998375, 13512928522, -7897799530], ![-58801712463, -18264280795, 73179771602], ![10592854405, -129697250934, 8761576249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8804839032488171127132227910140695, 854826879880078923811198569206007, 796981906587099526843027668570291]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![8804839032488171127132227910140695, 854826879880078923811198569206007, 796981906587099526843027668570291]] 
 ![![61, 0, 0], ![24, 1, 0], ![10, 0, 1]] where
  M :=![![![8804839032488171127132227910140695, 854826879880078923811198569206007, 796981906587099526843027668570291], ![65468206286728119995064610624035294, 6356048339433893149634974003794106, 5925943185867573069710219083806333], ![89107679961670901602814604919308126, 8651111025872136001336962553001769, 8065702099194050997257371142206120]]]
  hmulB := by decide  
  f := ![![![-109067056309274357, 100127323887681939, -62787387384262515]], ![![-121972880235872490, 38023543735671070, -15883946578368381]], ![![86672840589032560, -249466309737003, -8380964450749058]]]
  g := ![![![-322636477877126529717488761254203, 854826879880078923811198569206007, 796981906587099526843027668570291], ![-2398957142923951578578310759099780, 6356048339433893149634974003794106, 5925943185867573069710219083806333], ![-3265180420511489711505675537291730, 8651111025872136001336962553001769, 8065702099194050997257371142206120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4735945, 318893, 233671]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-4735945, 318893, 233671]] 
 ![![61, 0, 0], ![36, 1, 0], ![14, 0, 1]] where
  M :=![![![-4735945, 318893, 233671], ![19331466, -5522180, 2147029], ![31586886, 2399937, -4884394]]]
  hmulB := by decide  
  f := ![![![21819768521747, 2118394734569, 1975045841677]], ![![15536920058790, 1508417910628, 1406345320483]], ![![8627861146780, 837644799289, 780962514040]]]
  g := ![![![-319467, 318893, 233671], ![3083140, -5522180, 2147029], ![222470, 2399937, -4884394]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-20546951333, 13512928522, -7897799530]] ![![8804839032488171127132227910140695, 854826879880078923811198569206007, 796981906587099526843027668570291]]
  ![![-21819768521747, -2118394734569, -1975045841677]] where
 M := ![![![-21819768521747, -2118394734569, -1975045841677]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-21819768521747, -2118394734569, -1975045841677]] ![![-4735945, 318893, 233671]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [4, 62, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 17, 63], [55, 49, 4], [0, 1]]
 g := ![![[12, 41, 15], [14, 53, 16], [16, 62], [42, 35], [7, 1], []], ![[57, 66, 65, 41], [26, 65, 59, 11], [64, 65], [29, 40], [41, 56], [43, 16]], ![[56, 13, 5, 22], [28, 47, 47, 33], [20, 36], [15, 29], [50, 21], [35, 16]]]
 h' := ![![[19, 17, 63], [11, 29, 22], [38, 66, 63], [13, 9, 14], [39, 31, 54], [0, 0, 1], [0, 1]], ![[55, 49, 4], [30, 4, 24], [0, 11, 9], [16, 55, 47], [47, 15, 43], [55, 60, 49], [19, 17, 63]], ![[0, 1], [19, 34, 21], [34, 57, 62], [28, 3, 6], [17, 21, 37], [4, 7, 17], [55, 49, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 49], []]
 b := ![[], [57, 38, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [4, 62, 60, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![285614300, -7531336, 10033116]
  a := ![22, -1, 65]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4262900, -112408, 149748]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2596970962741, 252129604758, 235068337036]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![2596970962741, 252129604758, 235068337036]] 
 ![![71, 0, 0], ![0, 71, 0], ![26, 40, 1]] where
  M :=![![![2596970962741, 252129604758, 235068337036], ![19309726172396, 1874704683911, 1747845965584], ![26282145143576, 2551629171952, 2378963893427]]]
  hmulB := by decide  
  f := ![![![1626099, -142414, -56044]], ![![-4768348, 1880601, -910528]], ![![-2271910, 1001092, -511021]]]
  g := ![![![-49504307045, -128881744742, 235068337036], ![-368088294828, -958297661119, 1747845965584], ![-500998818106, -1304322909368, 2378963893427]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [50, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 70], [0, 1]]
 g := ![![[36, 27], [29, 4], [1, 54], [29], [57], [1]], ![[0, 44], [0, 67], [0, 17], [29], [57], [1]]]
 h' := ![![[46, 70], [41, 13], [21, 69], [66, 14], [5, 10], [21, 46], [0, 1]], ![[0, 1], [0, 58], [0, 2], [0, 57], [39, 61], [7, 25], [46, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [25, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [50, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![238, 33, 31]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -17, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1626099, 142414, 56044]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1626099, 142414, 56044]] 
 ![![71, 0, 0], ![43, 1, 0], ![7, 0, 1]] where
  M :=![![![-1626099, 142414, 56044], ![4768348, -1880601, 910528], ![12850264, 443744, -1595773]]]
  hmulB := by decide  
  f := ![![![-2596970962741, -252129604758, -235068337036]], ![![-1844781374229, -179102502655, -166982879692]], ![![-626210449053, -60796287398, -56682285249]]]
  g := ![![![-114679, 142414, 56044], ![1116345, -1880601, 910528], ![69573, 443744, -1595773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![2596970962741, 252129604758, 235068337036]] ![![-1626099, 142414, 56044]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119983272521051, 11648699778443, 10860448094457]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![119983272521051, 11648699778443, 10860448094457]] 
 ![![73, 0, 0], ![0, 73, 0], ![51, 45, 1]] where
  M :=![![![119983272521051, 11648699778443, 10860448094457], ![892133247113446, 86613676553694, 80752646765115], ![1214267632731322, 117888425671055, 109911076110580]]]
  hmulB := by decide  
  f := ![![![-10791285, 1131715, 234819]], ![![21048950, -12392638, 7025109]], ![![6760133, -6837836, 4355842]]]
  g := ![![![-5943829867072, -6535225540714, 10860448094457], ![-44195229286403, -48592540107897, 80752646765115], ![-60153386971346, -66138493141165, 109911076110580]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [50, 42, 1] where
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
 g := ![![[68, 19], [19], [3], [7, 72], [12], [1]], ![[0, 54], [19], [3], [49, 1], [12], [1]]]
 h' := ![![[31, 72], [3, 47], [2, 47], [15, 52], [2, 46], [23, 31], [0, 1]], ![[0, 1], [0, 26], [72, 26], [21, 21], [41, 27], [35, 42], [31, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [50, 42, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1343, 2937, 294]
  a := ![5, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-187, -141, 294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10791285, -1131715, -234819]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![10791285, -1131715, -234819]] 
 ![![73, 0, 0], ![21, 1, 0], ![52, 0, 1]] where
  M :=![![![10791285, -1131715, -234819], ![-21048950, 12392638, -7025109], ![-96642494, -789217, 10129208]]]
  hmulB := by decide  
  f := ![![![-119983272521051, -11648699778443, -10860448094457]], ![![-46736739315829, -4537484546589, -4230439133544]], ![![-102101339778438, -9912613892467, -9241840781128]]]
  g := ![![![640656, -1131715, -234819], ![1150840, 12392638, -7025109], ![-8312161, -789217, 10129208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![119983272521051, 11648699778443, 10860448094457]] ![![10791285, -1131715, -234819]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [15, 46, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 50, 69], [26, 28, 10], [0, 1]]
 g := ![![[58, 18, 65], [15, 5, 73], [15, 61, 46], [65, 7, 44], [25, 1], []], ![[31, 72, 8, 60], [41, 73, 38, 68], [2, 64, 5, 12], [60, 47, 25, 70], [42, 73], [78, 21]], ![[78, 55, 37, 32], [16, 5, 74, 51], [49, 8, 34, 18], [59, 34, 70, 10], [18, 51], [58, 21]]]
 h' := ![![[78, 50, 69], [12, 11, 67], [12, 72, 51], [52, 70, 21], [20, 20, 26], [0, 0, 1], [0, 1]], ![[26, 28, 10], [46, 1, 28], [45, 28, 76], [2, 17, 46], [21, 17, 54], [16, 26, 28], [78, 50, 69]], ![[0, 1], [19, 67, 63], [48, 58, 31], [10, 71, 12], [78, 42, 78], [43, 53, 50], [26, 28, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 18], []]
 b := ![[], [34, 42, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [15, 46, 54, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-885590, 102700, -46610]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11210, 1300, -590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB118I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB118I1 : PrimesBelowBoundCertificateInterval O 31 79 118 where
  m := 11
  g := ![2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB118I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
  β := ![I37N1, I53N0, I53N1, I53N2, I59N1, I61N0, I61N1, I61N2, I71N1, I73N1]
  Il := ![[I37N1], [], [], [], [I53N0, I53N1, I53N2], [I59N1], [I61N0, I61N1, I61N2], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
