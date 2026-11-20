import Metropolis.Asymptotic
import Metropolis.AsymptoticStatement
import Metropolis.ShellExpectation

open Filter
open scoped Asymptotics

namespace Metropolis.Asymptotic

theorem shell_scaling : ShellScalingStatement := by
  intro D hD p hp hp'
  have h (N : ℕ) := Shell.exact_escape hD N hp hp'.le
  simpa only [h, one_div] using exactSum_theta D hp hp'

theorem shell_scaling_one {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (fun N : ℕ => Shell.meanTime 1 N p 0) =Θ[atTop] (fun N : ℕ => (1/p)^N) := by
  simpa using (shell_scaling 1 (by decide) p hp hp')

theorem shell_scaling_two {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (fun N : ℕ => Shell.meanTime 2 N p 0) =Θ[atTop] (fun N : ℕ => (1/p)^N / (N:ℝ)) := by
  simpa using (shell_scaling 2 (by decide) p hp hp')

theorem shell_scaling_three {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (fun N : ℕ => Shell.meanTime 3 N p 0) =Θ[atTop]
      (fun N : ℕ => (1/p)^N / (N:ℝ)^2) := by
  simpa using (shell_scaling 3 (by decide) p hp hp')

end Metropolis.Asymptotic
