"""
Gauge invariance is not assumed -- it is checked directly. A random
SU(2)-valued gauge transformation g: V -> SU(2) is applied edge-wise as
U'(a,b) = g(a) . U(a,b) . g(b)^dagger, and the full spectrum (and hence
any moment built from it) must be unchanged.
"""
import numpy as np
import pytest

from graph.sg_graph import sg_tree_graph_with_faces
from operators.operators import build_su2_bundle
from su2.su2_utils import random_su2
from moments.moments import normalized_moment


@pytest.mark.parametrize("level,seed", [(2, 0), (3, 1), (3, 42)])
def test_spectrum_is_gauge_invariant(level, seed):
    theta = np.pi / 2
    rng = np.random.default_rng(seed)
    V, _E, _faces = sg_tree_graph_with_faces(level)
    n = len(V)
    gauge = [random_su2(rng) for _ in range(n)]

    H1, _ = build_su2_bundle(level, theta, commuting=False, gauge=None)
    H2, _ = build_su2_bundle(level, theta, commuting=False, gauge=gauge)

    w1 = np.linalg.eigvalsh(H1)
    w1.sort()
    w2 = np.linalg.eigvalsh(H2)
    w2.sort()

    assert np.max(np.abs(w1 - w2)) < 1e-10


@pytest.mark.parametrize("level,seed", [(2, 0), (3, 7)])
def test_M4_moment_is_gauge_invariant(level, seed):
    theta = np.pi / 2
    rng = np.random.default_rng(seed)
    V, _E, _faces = sg_tree_graph_with_faces(level)
    n = len(V)
    gauge = [random_su2(rng) for _ in range(n)]

    H1, n1 = build_su2_bundle(level, theta, commuting=False, gauge=None)
    H2, n2 = build_su2_bundle(level, theta, commuting=False, gauge=gauge)

    m4_1 = normalized_moment(H1, 2 * n1, 4)
    m4_2 = normalized_moment(H2, 2 * n2, 4)

    assert abs(m4_1 - m4_2) < 1e-9
