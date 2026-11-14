# Vendored kr-25 proof material

Fourteen Lean modules in this directory were copied from the local
`kr-25-ssm/lean` snapshot at commit
`56da0f89460922764785e3c61664bcb00ca9a77f` and migrated from Lean 4.32 to
Lean 4.33. They are needed by the CV18 sharp accelerated-moment proof
(`VolumeProofSharpMoments.lean`) and the radial truncation proof
(`VolumeProofRadialTruncation.lean`):

- `ArlibCommunity/Foundations/Convex/Localization/Analysis/ProductLocalization.lean`
- `Arlib/Convexity/GaussianCooling/{Variance,ZLogconcave,IndicatorVariance,LogConcaveProfileVariance}.lean`
- `Ttc/Volume/LVNormTail*.lean` (nine modules)

The shared localization foundation already maintained by the HitAndRun
development is reused rather than duplicated.

These modules previously lived under `ArlibCommunity/External/Kr25`. Their
imports now use the `ArlibCommunity.Algorithms.CV18.Analysis.Background`
module prefix. The build has no filesystem or Lake dependency on the source
snapshot.
