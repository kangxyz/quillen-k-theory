"""Reviewed CI identities, kept outside their own recipe hash tuple.

Adding an identity requires actual source review. Supporting-source correctness
remains a trusted-producer premise; hashing a candidate does not approve it.
"""
from lean_ci.github import EvidenceProtocol

LEGACY_HEAD = '69e542b48a1e7ba0a0a7648b5238b2a263cd22a6'
# Astra-admitted shared-recipe migration; tooling has its own workflow pin.
CORE_ENTRYPOINTS = {
    'scripts/check.sh': '7ee991c40b55bb5107b99500588153895ec9e484913123cc506c10c0d3044eb4',
    'scripts/check_run.py': '02fd64f30350514627c0550196c917b884b5cdbd5535fb3f6405208324e296e3',
    'scripts/ci_adapter.py': '736f982756ab1beb9d99a1eae41df4402df50b10d1d5632a10af5ea7127e47b0',
    'scripts/check_scope.py': 'bd39c54c17e82867c5047c99f546914474907be0c4903c342ad354a3942c5469',
    'scripts/dependency_scope.py': '6f6ac5e0277865bd0918fd4d32992ec108d388e607b98bd826fedeab3a8a3740',
    'scripts/library_sources.py': 'f2bb28db1f9329a66cd3174584cf9e000a61c50466e6747df4f54d3aeafe6e86',
    'scripts/generate_imports.py': '0b4ad1f0973d12f7ae64fc73a7206ec978eb541849cc6eb2d563bd9d4ca89576',
    'scripts/check_library_layout.py': '25c014ee3ab2387c609a095ed1b65d758a27f0624a9d0c7b8a26fb794446b509',
    'scripts/check_placeholders.py': '9b3f155d1eaa8d9506382e49f3382cc8f11dd257e1bd5da1336048e3af779c2e',
    'Tools/LintScoped.lean': '8980b027e274a5896d60edbe8b5f6e30cfb638369d9f199fccd87bc8f55aabef',
    'Tools/LintStyle.lean': '663e23f7c4d9a6cff5be7f6a76b460a4c5d9dc632d8aa011c73d934610da87bd',
    'QuillenTest/Axioms.lean': '4403edb9751e6dc8be050001210a491ebe75ac510e696df12a58e47102b34f60',
    'examples/downstream/Audit.lean': 'ebe7a0aaab7d95a70622a2ed53e4a35017426f7b345ecca01cb906047bc893e0',
}
PROTOCOL = EvidenceProtocol(
    workflow_path='.github/workflows/ci.yml', job_name='library',
    native_step='Build the complete library and audit the independent client',
    finalize_step='Finalize required check coverage',
    workflows={
        '6450d87a0f68bcb102396e39fbac2c0fcb648d8e4f71533606f71378705b144d': 'legacy',
        'd22c0280491733fc1c9c5f6100efd56d60bc5f10c6128aa7805549824a2445c3': 'core',
    },
    legacy_recipes={'scripts/check.sh': 'b074b4b75bddf912987c0867a2d357b2296b9a9d4c281226061077b2682d1621'},
    legacy_heads=frozenset({LEGACY_HEAD}),
    core_entrypoint_paths=tuple(CORE_ENTRYPOINTS),
    core_recipes=frozenset({tuple(CORE_ENTRYPOINTS.values())}))
