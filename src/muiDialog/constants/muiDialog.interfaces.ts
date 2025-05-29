import {
  CONFIRMATION_SUBTYPES,
  INFORMATION_SUBTYPES,
  INPUT_SUBTYPES,
  MODAL_TYPES,
  ModalSize,
  TERTIARY_CTA_TYPES,
} from "./muiDialog.types";

interface IActions {
  primaryCtaTitle?: string;
  secondaryCtaTitle?: string;
  isPrimaryCtaLoading?: boolean;
  isPrimaryCtaDisabled?: boolean;
  isSecondaryCtaDisabled?: boolean;
  isSecondaryCtaLoading?: boolean;
  onPrimaryCtaClick?: () => void;
  onSecondaryCtaClick?: () => void;
  tertiaryCtaTitle?: string;
  tertiaryCtaStartIcon?: React.ReactNode;
  isTertiaryCtaLoading?: boolean;
  isTertiaryCtaDisabled?: boolean;
  onTertiaryCtaClick?: () => void;
}
export interface BaseModalProps {
  wrapperClassName?: string;
  onClose: () => void;
  open: boolean;
  showCloseIcon?: boolean;
  title?: string | React.ReactNode;
  subTitle?: string | React.ReactNode;
  description?: string | React.ReactNode;
  children: React.ReactNode;
  actions?: IActions;
  showDivider?: boolean;
  showActions?: boolean;
}

export interface InformationModalProps extends BaseModalProps {
  type: typeof MODAL_TYPES.INFORMATION;
  subtype: (typeof INFORMATION_SUBTYPES)[keyof typeof INFORMATION_SUBTYPES];
  size?: ModalSize;
  tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}

export interface ConfirmationModalProps extends BaseModalProps {
  type: typeof MODAL_TYPES.CONFIRMATION;
  subtype: (typeof CONFIRMATION_SUBTYPES)[keyof typeof CONFIRMATION_SUBTYPES];
  size?: ModalSize;
  tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}

export interface InputModalProps extends BaseModalProps {
  type: typeof MODAL_TYPES.INPUT;
  subtype: (typeof INPUT_SUBTYPES)[keyof typeof INPUT_SUBTYPES];
  size?: ModalSize;
  tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}
