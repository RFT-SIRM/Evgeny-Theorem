"""Minimal SU(2) utilities: Pauli matrices and rotation generators."""
import numpy as np

I2 = np.eye(2, dtype=complex)
SIGMA_X = np.array([[0, 1], [1, 0]], dtype=complex)
SIGMA_Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
SIGMA_Z = np.array([[1, 0], [0, -1]], dtype=complex)
PAULI = [SIGMA_X, SIGMA_Y, SIGMA_Z]


def su2_rotation(axis: int, theta: float) -> np.ndarray:
    """
    Return exp(-i * theta/2 * sigma_axis) as a 2x2 unitary matrix,
    axis in {0,1,2} for x,y,z.
    """
    return np.cos(theta / 2) * I2 - 1j * np.sin(theta / 2) * PAULI[axis]


def random_su2(rng: np.random.Generator) -> np.ndarray:
    """Draw a Haar-random SU(2) element via a random unit quaternion."""
    v = rng.standard_normal(4)
    v /= np.linalg.norm(v)
    return v[0] * I2 - 1j * (v[1] * SIGMA_X + v[2] * SIGMA_Y + v[3] * SIGMA_Z)
