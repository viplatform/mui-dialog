import {
  INFORMATION_SUBTYPES,
  MODAL_SIZES,
  MODAL_TYPES,
} from "../constants/muiDialog.types";

export const checkIfTertiaryCtaIsAllowed = (
  type: string,
  subtype: string,
  size: string
) => {
  if (type === MODAL_TYPES.CONFIRMATION) return false;

  if (subtype === INFORMATION_SUBTYPES.ACKNOWLEDGEMENT) return false;

  if (size === MODAL_SIZES.SMALL) return false;

  return true;
};
