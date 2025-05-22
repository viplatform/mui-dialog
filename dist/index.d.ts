import * as react_jsx_runtime from 'react/jsx-runtime';
import { Breakpoint } from '@mui/material';

declare const MODAL_TYPES: {
    readonly INFORMATION: "information";
    readonly CONFIRMATION: "confirmation";
    readonly INPUT: "input";
};
type ModalType = (typeof MODAL_TYPES)[keyof typeof MODAL_TYPES];
declare const INFORMATION_SUBTYPES: {
    readonly ACKNOWLEDGEMENT: "acknowledgement";
    readonly PROGRESS: "progress";
    readonly PASSIVE: "passive";
};
declare const CONFIRMATION_SUBTYPES: {
    readonly DEFAULT: "default";
    readonly DESTRUCTIVE: "destructive";
    readonly NESTED: "nested";
};
declare const INPUT_SUBTYPES: {
    readonly DEFAULT: "default";
    readonly DESTRUCTIVE: "destructive";
};
type InformationSubtype = (typeof INFORMATION_SUBTYPES)[keyof typeof INFORMATION_SUBTYPES];
type ConfirmationSubtype = (typeof CONFIRMATION_SUBTYPES)[keyof typeof CONFIRMATION_SUBTYPES];
type InputSubtype = (typeof INPUT_SUBTYPES)[keyof typeof INPUT_SUBTYPES];
declare const MODAL_SIZES: {
    readonly SMALL: "small";
    readonly MEDIUM: "medium";
    readonly LARGE: "large";
    readonly EXTRA_LARGE: "extraLarge";
};
declare const TERTIARY_CTA_TYPES: {
    DEFAULT: string;
    DESTRUCTIVE: string;
};
type ModalSize = (typeof MODAL_SIZES)[keyof typeof MODAL_SIZES];
type ModalConfig = {
    DISMISSIBLE: 'full' | 'partial';
    ALLOWED_SIZES: ModalSize[];
};
type ModalTypeConfig = {
    [subtype: string]: ModalConfig;
};
declare const MODAL_CONFIGS: Record<ModalType, ModalTypeConfig>;
declare const SIZE_TO_MAX_WIDTH: Record<ModalSize, Breakpoint>;
type SubtypeForType<T extends ModalType> = T extends typeof MODAL_TYPES.INFORMATION ? InformationSubtype : T extends typeof MODAL_TYPES.CONFIRMATION ? ConfirmationSubtype : T extends typeof MODAL_TYPES.INPUT ? InputSubtype : never;
declare const MODAL_SIZE_VS_CLASS_NAMES: {
    small: string;
    medium: string;
    large: string;
    extraLarge: string;
};

interface IActions {
    primaryCtaTitle?: string;
    secondaryCtaTitle?: string;
    isPrimaryCtaLoading?: boolean;
    isPrimaryCtaDisabled?: boolean;
    isSecondaryCtaDisabled?: boolean;
    onPrimaryCtaClick?: () => void;
    onSecondaryCtaClick?: () => void;
    tertiaryCtaTitle?: string;
    tertiaryCtaStartIcon?: React.ReactNode;
    isTertiaryCtaLoading?: boolean;
    isTertiaryCtaDisabled?: boolean;
    onTertiaryCtaClick?: () => void;
}
interface BaseModalProps {
    wrapperClassName?: string;
    onClose: () => void;
    open: boolean;
    showCloseIcon?: boolean;
    title?: string;
    subTitle?: string | React.ReactNode;
    description?: string;
    children: React.ReactNode;
    actions?: IActions;
    showDivider?: boolean;
    showActions?: boolean;
}
interface InformationModalProps extends BaseModalProps {
    type: typeof MODAL_TYPES.INFORMATION;
    subtype: (typeof INFORMATION_SUBTYPES)[keyof typeof INFORMATION_SUBTYPES];
    size?: ModalSize;
    tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}
interface ConfirmationModalProps extends BaseModalProps {
    type: typeof MODAL_TYPES.CONFIRMATION;
    subtype: (typeof CONFIRMATION_SUBTYPES)[keyof typeof CONFIRMATION_SUBTYPES];
    size?: ModalSize;
    tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}
interface InputModalProps extends BaseModalProps {
    type: typeof MODAL_TYPES.INPUT;
    subtype: (typeof INPUT_SUBTYPES)[keyof typeof INPUT_SUBTYPES];
    size?: ModalSize;
    tertiaryCtaType?: (typeof TERTIARY_CTA_TYPES)[keyof typeof TERTIARY_CTA_TYPES];
}

type ModalProps = InformationModalProps | ConfirmationModalProps | InputModalProps;
declare const ViDialog: (props: ModalProps) => react_jsx_runtime.JSX.Element;
//# sourceMappingURL=index.d.ts.map

export { CONFIRMATION_SUBTYPES, INFORMATION_SUBTYPES, INPUT_SUBTYPES, MODAL_CONFIGS, MODAL_SIZES, MODAL_SIZE_VS_CLASS_NAMES, MODAL_TYPES, SIZE_TO_MAX_WIDTH, TERTIARY_CTA_TYPES, ViDialog };
export type { BaseModalProps, ConfirmationModalProps, ConfirmationSubtype, InformationModalProps, InformationSubtype, InputModalProps, InputSubtype, ModalSize, ModalType, SubtypeForType };
