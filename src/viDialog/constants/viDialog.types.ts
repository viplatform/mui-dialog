import { Breakpoint } from '@mui/material';

export const MODAL_TYPES = {
  INFORMATION: 'information',
  CONFIRMATION: 'confirmation',
  INPUT: 'input',
} as const;

export type ModalType = (typeof MODAL_TYPES)[keyof typeof MODAL_TYPES];

export const INFORMATION_SUBTYPES = {
  ACKNOWLEDGEMENT: 'acknowledgement',
  PROGRESS: 'progress',
  PASSIVE: 'passive',
} as const;

export const CONFIRMATION_SUBTYPES = {
  DEFAULT: 'default',
  DESTRUCTIVE: 'destructive',
  NESTED: 'nested',
} as const;

export const INPUT_SUBTYPES = {
  DEFAULT: 'default',
  DESTRUCTIVE: 'destructive',
} as const;

export type InformationSubtype = (typeof INFORMATION_SUBTYPES)[keyof typeof INFORMATION_SUBTYPES];
export type ConfirmationSubtype =
  (typeof CONFIRMATION_SUBTYPES)[keyof typeof CONFIRMATION_SUBTYPES];

export type InputSubtype = (typeof INPUT_SUBTYPES)[keyof typeof INPUT_SUBTYPES];

export const MODAL_SIZES = {
  SMALL: 'small',
  MEDIUM: 'medium',
  LARGE: 'large',
  EXTRA_LARGE: 'extraLarge',
} as const;

export const TERTIARY_CTA_TYPES = {
  DEFAULT: 'default',
  DESTRUCTIVE: 'destructive',
};

export type ModalSize = (typeof MODAL_SIZES)[keyof typeof MODAL_SIZES];

type ModalConfig = {
  DISMISSIBLE: 'full' | 'partial';
  ALLOWED_SIZES: ModalSize[];
};

type ModalTypeConfig = {
  [subtype: string]: ModalConfig;
};

export const MODAL_CONFIGS: Record<ModalType, ModalTypeConfig> = {
  [MODAL_TYPES.INFORMATION]: {
    [INFORMATION_SUBTYPES.ACKNOWLEDGEMENT]: {
      DISMISSIBLE: 'full',
      ALLOWED_SIZES: [MODAL_SIZES.SMALL],
    },
    [INFORMATION_SUBTYPES.PROGRESS]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: [MODAL_SIZES.SMALL, MODAL_SIZES.MEDIUM, MODAL_SIZES.LARGE],
    },
    [INFORMATION_SUBTYPES.PASSIVE]: {
      DISMISSIBLE: 'full',
      ALLOWED_SIZES: [MODAL_SIZES.MEDIUM, MODAL_SIZES.LARGE, MODAL_SIZES.EXTRA_LARGE],
    },
  },
  [MODAL_TYPES.CONFIRMATION]: {
    [CONFIRMATION_SUBTYPES.DEFAULT]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: [MODAL_SIZES.SMALL],
    },
    [CONFIRMATION_SUBTYPES.DESTRUCTIVE]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: [MODAL_SIZES.SMALL],
    },
    [CONFIRMATION_SUBTYPES.NESTED]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: [MODAL_SIZES.SMALL],
    },
  },
  [MODAL_TYPES.INPUT]: {
    [INPUT_SUBTYPES.DEFAULT]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: Object.values(MODAL_SIZES),
    },
    [INPUT_SUBTYPES.DESTRUCTIVE]: {
      DISMISSIBLE: 'partial',
      ALLOWED_SIZES: Object.values(MODAL_SIZES),
    },
  },
};

export const SIZE_TO_MAX_WIDTH: Record<ModalSize, Breakpoint> = {
  [MODAL_SIZES.SMALL]: 'xs',
  [MODAL_SIZES.MEDIUM]: 'sm',
  [MODAL_SIZES.LARGE]: 'md',
  [MODAL_SIZES.EXTRA_LARGE]: 'lg',
};

export type SubtypeForType<T extends ModalType> = T extends typeof MODAL_TYPES.INFORMATION
  ? InformationSubtype
  : T extends typeof MODAL_TYPES.CONFIRMATION
  ? ConfirmationSubtype
  : T extends typeof MODAL_TYPES.INPUT
  ? InputSubtype
  : never;

export const MODAL_SIZE_VS_CLASS_NAMES = {
  [MODAL_SIZES.SMALL]: 'small',
  [MODAL_SIZES.MEDIUM]: 'medium',
  [MODAL_SIZES.LARGE]: 'large',
  [MODAL_SIZES.EXTRA_LARGE]: 'extra-large',
};
